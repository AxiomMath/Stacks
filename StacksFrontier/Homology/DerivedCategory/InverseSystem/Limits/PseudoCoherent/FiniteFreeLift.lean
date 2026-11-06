module

public import Mathlib
public import StacksCore.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletionKoszul
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.Perfect.Lifting
public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Module.Projective.Lifting
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Pseudo-coherence of a derived inverse limit: finite free lifts and derived transposes

Let `(Aₙ)` be an inverse system of commutative rings with surjective transition maps whose
kernels are locally nilpotent, and let `(Kₙ)` be a compatible inverse system of objects of the
derived categories `D(Aₙ)` whose transition maps induce isomorphisms `Kₙ₊₁ ⊗ᴸ[Aₙ₊₁] Aₙ ≅ Kₙ`.
If every `Kₙ` is pseudo-coherent, or one of them is and all subsequent transition kernels are
nilpotent, then a derived inverse limit of `(Kₙ)` over the limit ring is pseudo-coherent, and its
canonical derived base-change map to each `Kₙ` is an isomorphism. When the limit ring is adically
complete and the tower is the tower of its quotients by the powers of the ideal, the derived
inverse limit is moreover derived complete.

This file contains the first steps: finite free lifts across a surjection with locally nilpotent
kernel realizing a prescribed isomorphism after reduction, and the derived transposes of chain
maps along an additive adjunction.

## Main definitions

* `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp`: the canonical natural comparison
  identifying successive derived restrictions of scalars with restriction along the composite.
* `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison`: the adjoint transpose of a
  morphism into a derived restriction of scalars.
* `StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction`: the adjunction induced on
  cochain complexes by an adjunction of additive functors.

## Implementation notes

The inverse system of rings is a functor on `ℕᵒᵖ` and the limit ring is presented by an arbitrary
limit cone, so no particular construction of the limit is privileged. Restriction of scalars to
the limit ring uses the natural composition isomorphism obtained by localizing restriction of
scalars on complexes. A derived inverse limit is supplied together with its Milnor distinguished
triangle, whose middle map is `1 - shift` on the product of the restricted terms; the comparison
to the `n`-th term is the adjoint transpose of that triangle's projection. The rings lie in
universe `u` and the modules in the independent ambient universe `max u v`, which contains the
rings and allows modules of arbitrarily larger size.

## References

* [The Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
* [The Stacks Project, Tag 09AV](https://stacks.math.columbia.edu/tag/09AV)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace StacksDraft.DerivedInverseLimit

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

/-- The canonical natural isomorphism from successive derived restrictions of scalars to
restriction along their composite. It is obtained by localizing the degreewise identity
`ModuleCat.restrictScalarsComp'`. -/
public noncomputable abbrev derivedRestrictScalarsComp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (w : h = g.comp f) :
    (ModuleCat.restrictScalars.{max u v} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max u v} h).mapDerivedCategory :=
  let F := ModuleCat.restrictScalars.{max u v} g
  let G := ModuleCat.restrictScalars.{max u v} f
  let H := ModuleCat.restrictScalars.{max u v} h
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} T) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp' f g h w).symm (ComplexShape.up ℤ)) _ ≪≫
      H.mapDerivedCategoryFactors.symm)

/-- The base-change morphism adjoint to the given morphism into a derived restriction of
scalars. This uses the derived extension/restriction adjunction. -/
public noncomputable abbrev derivedBaseChangeComparison
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {X : DerivedCategory (ModuleCat.{max u v w} R)} {Y : DerivedCategory (ModuleCat.{max u v w} S)}
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f).functor.obj
      X ⟶ Y := by
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, w} f
  have hD : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  let adj := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, w, v}
    R S _ _ f _ _ D.functor D.comparison hD
  exact (adj.homEquiv X Y).symm g

/-- The induction step in the proof of 0CQF: the finite free lift realizes the given
isomorphism after derived reduction. In particular this retains the transition map chosen
in the tower, not just the isomorphism classes of its two objects. -/
public theorem exists_finiteFree_lift_representing_iso
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hE : PseudoCoherence.IsBoundedAboveFiniteFree E)
    (e : DerivedCategory.Q.obj E ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I)).functor.obj K)
    (hK : PseudoCoherence.IsPseudoCoherent K) (hI : ∀ x : R, x ∈ I → IsUnit (1 + x)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      PseudoCoherence.IsBoundedAboveFiniteFree P ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).comparison.app P ≫
          DerivedCategory.Q.map eRed.hom ≫ e.hom =
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).functor.map eK.hom := by
  have hterms (i : ℤ) : Module.Finite (R ⧸ I) (E.X i) ∧
      Module.IsStablyFree (R ⧸ I) (E.X i) := by
    let := (hE.finiteFree i).2
    exact ⟨(hE.finiteFree i).1, inferInstance⟩
  obtain ⟨P, hP, hb, eRed, eK, hcompat, hfree⟩ :=
    StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing_iso I
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I)) K E hE.upperBound hterms e hK hI
  exact ⟨P, ⟨hb, fun i => ⟨(hP i).1, hfree i (hE.finiteFree i).2⟩⟩,
    eRed, eK, hcompat⟩

lemma exists_linearEquiv_pi_of_compatible_coordinates
    {J : Type w} [Category.{w'} J] (A : J ⥤ CommRingCat.{u})
    (c : Cone A) (hc : IsLimit c) (ι : Type v)
    (M : J ⥤ ModuleCat.{max u v} c.pt)
    [PreservesLimit M (forget (ModuleCat.{max u v} c.pt))] (d : Cone M) (hd : IsLimit d)
    (e : ∀ j, (ModuleCat.restrictScalars.{max u v} (c.π.app j).hom).obj
      (ModuleCat.of (A.obj j) (ι → A.obj j)) ≅ M.obj j)
    (he : ∀ {j k} (f : j ⟶ k) (x : M.obj j) (i : ι),
      (e k).inv (M.map f x) i = (A.map f).hom ((e j).inv x i)) :
    ∃ E : d.pt ≃ₗ[c.pt] (ι → c.pt),
      ∀ (x : d.pt) (j : J) (i : ι),
        (c.π.app j).hom (E x i) = (e j).inv (d.π.app j x) i := by
  let er : c.pt ≃ (A ⋙ forget CommRingCat.{u}).sections :=
    Types.isLimitEquivSections (isLimitOfPreserves (forget CommRingCat.{u}) hc)
  have her (s : (A ⋙ forget CommRingCat.{u}).sections) (j : J) :
      (c.π.app j).hom (er.symm s) = s.val j :=
    Types.isLimitEquivSections_symm_apply (isLimitOfPreserves (forget CommRingCat.{u}) hc) s j
  let em : d.pt ≃ (M ⋙ forget (ModuleCat.{max u v} c.pt)).sections :=
    Types.isLimitEquivSections (isLimitOfPreserves (forget (ModuleCat.{max u v} c.pt)) hd)
  have heinv (j : J) (z : ι → A.obj j) : (e j).inv ((e j).hom z) = z :=
    ConcreteCategory.congr_hom (e j).hom_inv_id z
  let s (x : d.pt) (i : ι) : (A ⋙ forget CommRingCat.{u}).sections :=
    ⟨fun j ↦ (e j).inv (d.π.app j x) i, fun {j k} f ↦ by
      show (A.map f).hom ((e j).inv (d.π.app j x) i) =
        (e k).inv (d.π.app k x) i
      rw [← he f]
      exact congrArg (fun z ↦ (e k).inv z i) (ConcreteCategory.congr_hom (d.w f) x)⟩
  let l : d.pt →ₗ[c.pt] (ι → c.pt) :=
    { toFun x i := er.symm (s x i)
      map_add' x y := by
        funext i
        apply Concrete.isLimit_ext A hc
        intro j
        show (c.π.app j).hom (er.symm (s (x + y) i)) =
          (c.π.app j).hom (er.symm (s x i) + er.symm (s y i))
        rw [map_add, her, her, her]
        show (e j).inv (d.π.app j (x + y)) i = _
        rw [map_add, map_add]
        rfl
      map_smul' a x := by
        funext i
        apply Concrete.isLimit_ext A hc
        intro j
        show (c.π.app j).hom (er.symm (s (a • x) i)) =
          (c.π.app j).hom (a * er.symm (s x i))
        rw [map_mul, her, her]
        show (e j).inv (d.π.app j (a • x)) i = _
        rw [map_smul, map_smul]
        rfl }
  have hl (x : d.pt) (j : J) (i : ι) :
      (c.π.app j).hom (l x i) = (e j).inv (d.π.app j x) i :=
    her (s x i) j
  have hinj : Function.Injective l := by
    intro x y hxy
    apply Concrete.isLimit_ext M hd
    intro j
    apply (e j).toLinearEquiv.symm.injective
    funext i
    show (e j).inv (d.π.app j x) i = (e j).inv (d.π.app j y) i
    rw [← hl, ← hl, hxy]
  have hsurj : Function.Surjective l := by
    intro x
    let t : (M ⋙ forget (ModuleCat.{max u v} c.pt)).sections :=
      ⟨fun j ↦ (e j).hom (fun i ↦ (c.π.app j).hom (x i)), fun {j k} f ↦ by
        show M.map f ((e j).hom _) = (e k).hom _
        apply (e k).toLinearEquiv.symm.injective
        funext i
        show (e k).inv (M.map f ((e j).hom _)) i = (e k).inv ((e k).hom _) i
        rw [he, heinv, heinv]
        exact ConcreteCategory.congr_hom (c.w f) (x i)⟩
    refine ⟨em.symm t, ?_⟩
    funext i
    apply Concrete.isLimit_ext A hc
    intro j
    rw [hl]
    have ht : d.π.app j (em.symm t) = t.val j :=
      Types.isLimitEquivSections_symm_apply
        (isLimitOfPreserves (forget (ModuleCat.{max u v} c.pt)) hd) t j
    rw [ht]
    show (e j).inv ((e j).hom _) i = _
    exact congrFun (heinv j _) i
  exact ⟨LinearEquiv.ofBijective l ⟨hinj, hsurj⟩, hl⟩

private lemma exists_linearEquiv_lifting_quotient
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    (e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R]
      (N ⧸ I • (⊤ : Submodule R N))) :
    ∃ E : M ≃ₗ[R] N, ∀ x : M,
      Submodule.Quotient.mk (E x) = e (Submodule.Quotient.mk x) := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R N)).mkQ
    (e.toLinearMap.comp (I • (⊤ : Submodule R M)).mkQ)
    (Submodule.mkQ_surjective _)
  have he : inducedQuot I f = e.toLinearMap := by
    ext x
    exact LinearMap.congr_fun hf x
  refine ⟨LinearEquiv.ofBijective f (lift_iso_of_quot_iso I hI f ?_), ?_⟩
  · rw [he]
    exact e.bijective
  · intro x
    exact LinearMap.congr_fun hf x

private def extendScalarsQuotientIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{max u v} R) :
    (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M) ≅
      ModuleCat.of R (M ⧸ RingHom.ker f • (⊤ : Submodule R M)) := by
  let e := RingHom.quotientKerEquivOfSurjective hf
  let er : (R ⧸ RingHom.ker f) ≃ₗ[R]
      (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) :=
    { __ := e
      map_smul' r x := by
        change e (r • x) = f r * e x
        change e (Ideal.Quotient.mk _ r * x) = _
        rw [map_mul]
        rfl }
  exact ((TensorProduct.congr er.symm (LinearEquiv.refl R M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f))).toModuleIso

private lemma extendScalarsQuotientIso_one_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{max u v} R) (x : M) :
    (extendScalarsQuotientIso f hf M).hom
        ((ModuleCat.extendRestrictScalarsAdj f).unit.app M x) =
      Submodule.Quotient.mk x := by
  show TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f)
    ((RingHom.quotientKerEquivOfSurjective hf).symm 1 ⊗ₜ[R] x) = _
  rw [map_one, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

private lemma exists_iso_lifting_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    (hI : ∀ x ∈ RingHom.ker f, IsUnit (1 + x))
    (M N : ModuleCat.{max u v} R)
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (e : (ModuleCat.extendScalars f).obj M ≅ (ModuleCat.extendScalars f).obj N) :
    ∃ E : M ≅ N, (ModuleCat.extendScalars f).map E.hom = e.hom := by
  let eM := extendScalarsQuotientIso f hf M
  let eN := extendScalarsQuotientIso f hf N
  let eq := eM.symm ≪≫ (ModuleCat.restrictScalars f).mapIso e ≪≫ eN
  obtain ⟨E, hE⟩ := exists_linearEquiv_lifting_quotient (RingHom.ker f) hI eq.toLinearEquiv
  refine ⟨E.toModuleIso, ?_⟩
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply eN.toLinearEquiv.injective
  have hunit := extendScalarsQuotientIso_one_tmul f hf N (E x)
  show eN.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app N (E x)) = _
  rw [hunit, hE]
  show eN.hom (e.hom (eM.inv (Submodule.Quotient.mk x))) = _
  have hx : eM.inv (Submodule.Quotient.mk x) =
      (ModuleCat.extendRestrictScalarsAdj f).unit.app M x := by
    apply eM.toLinearEquiv.injective
    show eM.hom (eM.inv _) = _
    rw [← ConcreteCategory.comp_apply, eM.inv_hom_id]
    exact (extendScalarsQuotientIso_one_tmul f hf M x).symm
  rw [hx]
  rfl

private def extendScalarsPiIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (ι : Type v) [Fintype ι] :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (ι → R)) ≅
      ModuleCat.of S (ι → S) := by
  letI := f.toAlgebra
  exact ((Pi.basisFun R ι).baseChange S).equivFun.toModuleIso

private lemma extendScalarsPiIso_one_tmul
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (ι : Type v) [Fintype ι] (x : ι → R) (i : ι) :
    (extendScalarsPiIso f ι).hom
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app (ModuleCat.of R (ι → R)) x) i =
        f (x i) := by
  let := f.toAlgebra
  show (((Pi.basisFun R ι).baseChange S).equivFun ((1 : S) ⊗ₜ[R] x)) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
  simp only [Pi.basisFun_repr]
  show f (x i) * 1 = f (x i)
  exact mul_one _

private lemma exists_coordinates_lifting_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    (hI : ∀ x ∈ RingHom.ker f, IsUnit (1 + x))
    (M : ModuleCat.{max u v} R) [Module.Finite R M] [Module.Projective R M]
    (ι : Type v) [Fintype ι]
    (e : (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S (ι → S)) :
    ∃ E : M ≅ ModuleCat.of R (ι → R), ∀ x : M, ∀ i : ι,
      f (E.hom x i) = e.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app M x) i := by
  obtain ⟨E, hE⟩ := exists_iso_lifting_extendScalars f hf hI M
    (ModuleCat.of R (ι → R)) (e ≪≫ (extendScalarsPiIso f ι).symm)
  refine ⟨E, fun x i ↦ ?_⟩
  have h : (ModuleCat.extendScalars f).map E.hom ≫ (extendScalarsPiIso f ι).hom =
      e.hom := by rw [hE]; simp
  have hx := congrArg (fun g ↦ g i) (ConcreteCategory.congr_hom h
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app M x))
  exact (extendScalarsPiIso_one_tmul f ι (E.hom x) i).symm.trans hx

lemma exists_compatible_coordinates
    (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
    (hf : ∀ n, Function.Surjective (f n))
    (hI : ∀ n, ∀ x ∈ RingHom.ker (f n), IsUnit (1 + x))
    (M : ∀ n, ModuleCat.{max u v} (R n))
    [∀ n, Module.Finite (R n) (M n)] [∀ n, Module.Projective (R n) (M n)]
    (g : ∀ n, M (n + 1) ⟶ (ModuleCat.restrictScalars (f n)).obj (M n))
    (hg : ∀ n, IsIso (((ModuleCat.extendRestrictScalarsAdj (f n)).homEquiv _ _).symm (g n)))
    (ι : Type v) [Fintype ι] (e₀ : M 0 ≅ ModuleCat.of (R 0) (ι → R 0)) :
    ∃ e : ∀ n, M n ≅ ModuleCat.of (R n) (ι → R n),
      e 0 = e₀ ∧ ∀ n (x : M (n + 1)) (i : ι),
        (f n) ((e (n + 1)).hom x i) = (e n).hom (g n x) i := by
  have hs (n : ℕ) (e : M n ≅ ModuleCat.of (R n) (ι → R n)) :
      ∃ E : M (n + 1) ≅ ModuleCat.of (R (n + 1)) (ι → R (n + 1)),
        ∀ x i, f n (E.hom x i) = e.hom (g n x) i := by
    have := hg n
    let a := asIso (((ModuleCat.extendRestrictScalarsAdj (f n)).homEquiv _ _).symm (g n))
    obtain ⟨E, hE⟩ := exists_coordinates_lifting_extendScalars
      (f n) (hf n) (hI n) (M (n + 1)) ι (a ≪≫ e)
    refine ⟨E, fun x i ↦ ?_⟩
    rw [hE]
    have he := ConcreteCategory.congr_hom
      (((ModuleCat.extendRestrictScalarsAdj (f n)).homEquiv _ _).apply_symm_apply (g n)) x
    change a.hom ((ModuleCat.extendRestrictScalarsAdj (f n)).unit.app _ x) = g n x at he
    show e.hom (a.hom _) i = e.hom (g n x) i
    rw [he]
  let e : ∀ n, M n ≅ ModuleCat.of (R n) (ι → R n) :=
    Nat.rec e₀ (fun n e ↦ (hs n e).choose)
  exact ⟨e, rfl, fun n ↦ (hs n (e n)).choose_spec⟩

lemma isIso_baseChange_of_coordinates
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{max u v} R) (N : ModuleCat.{max u v} S)
    (ι : Type v) [Fintype ι]
    (eM : M ≅ ModuleCat.of R (ι → R)) (eN : N ≅ ModuleCat.of S (ι → S))
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N)
    (hg : ∀ x i, eN.hom (g x) i = f (eM.hom x i)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g) := by
  let e := (ModuleCat.extendScalars f).mapIso eM ≪≫ extendScalarsPiIso f ι ≪≫ eN.symm
  suffices h : ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g = e.hom by
    rw [h]
    infer_instance
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).injective
  rw [Equiv.apply_symm_apply]
  ext x
  apply eN.toLinearEquiv.injective
  ext i
  show eN.hom (g x) i = eN.hom (eN.inv ((extendScalarsPiIso f ι).hom
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app _ (eM.hom x)))) i
  rw [← ConcreteCategory.comp_apply, eN.inv_hom_id]
  exact (hg x i).trans (extendScalarsPiIso_one_tmul f ι (eM.hom x) i).symm

/-- For a tower of surjections of modules, the difference map `(xₙ) ↦ (xₙ - g xₙ₊₁)` on the
product is an epimorphism: one solves for the coordinates by recursion. -/
lemma epi_pi_difference_of_surjective
    {R : Type u} [Ring R] (M : ℕ → ModuleCat.{v} R)
    (g : ∀ n, M (n + 1) ⟶ M n) (hg : ∀ n, Function.Surjective (g n)) :
    Epi (Pi.lift fun n ↦ Pi.π M n - Pi.π M (n + 1) ≫ g n) := by
  classical
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  let y : ∀ n, M n := Nat.rec 0 (fun n y ↦ (hg n (y - Pi.π M n x)).choose)
  let z := (ModuleCat.piIsoPi M).inv y
  refine ⟨z, ?_⟩
  have hz (n : ℕ) : Pi.π M n z = y n :=
    ConcreteCategory.congr_hom (ModuleCat.piIsoPi_inv_kernel_ι M n) y
  apply Concrete.isLimit_ext (Discrete.functor M) (limit.isLimit _)
  intro ⟨n⟩
  show Pi.π M n ((Pi.lift fun n ↦ Pi.π M n - Pi.π M (n + 1) ≫ g n) z) =
    Pi.π M n x
  rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]
  show Pi.π M n z - g n (Pi.π M (n + 1) z) = Pi.π M n x
  rw [hz, hz]
  rw [(hg n (y n - Pi.π M n x)).choose_spec]
  abel

/-- Extension along a surjection agrees with reduction modulo its kernel, transported along
the quotient equivalence. -/
public def extendScalarsQuotientKerIso
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) :
    ModuleCat.extendScalars.{u, u, max u v w} (Ideal.Quotient.mk (RingHom.ker f)) ≅
      ModuleCat.extendScalars.{u, w, max u v w} f ⋙
        ModuleCat.restrictScalars (RingHom.quotientKerEquivOfSurjective hf).toRingHom := by
  let e := RingHom.quotientKerEquivOfSurjective hf
  let E : ModuleCat.{max u v w} S ≌ ModuleCat.{max u v w} (R ⧸ RingHom.ker f) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let adj := (ModuleCat.extendRestrictScalarsAdj.{max u v w} f).comp E.toAdjunction
  let eq := (ModuleCat.restrictScalarsComp' f e.symm.toRingHom
    (Ideal.Quotient.mk (RingHom.ker f))
    (RingHom.quotientKerEquivOfSurjective_symm_comp hf).symm).symm
  exact Adjunction.leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{max u v w} (Ideal.Quotient.mk (RingHom.ker f)))
    (adj.ofNatIsoRight eq)

/-- The quotient-kernel comparison preserves the extension/restriction unit. -/
public lemma extendScalarsQuotientKerIso_one_tmul
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{max u v w} R) (x : M) :
    (extendScalarsQuotientKerIso.{u, v, w} f hf).hom.app M
      ((ModuleCat.extendRestrictScalarsAdj.{max u v w} (Ideal.Quotient.mk (RingHom.ker f))).unit.app
        M x) =
      (ModuleCat.extendRestrictScalarsAdj.{max u v w} f).unit.app M x := by
  have h := ConcreteCategory.congr_hom
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (ModuleCat.extendRestrictScalarsAdj.{max u v w} (Ideal.Quotient.mk (RingHom.ker f)))
      (((ModuleCat.extendRestrictScalarsAdj.{max u v w} f).comp
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (RingHom.quotientKerEquivOfSurjective hf)).toAdjunction).ofNatIsoRight
            (ModuleCat.restrictScalarsComp' f
              (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
              (Ideal.Quotient.mk (RingHom.ker f))
              (RingHom.quotientKerEquivOfSurjective_symm_comp hf).symm).symm) M) x
  exact h

private lemma isZero_of_isZero_quotient_extendScalars
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (M : ModuleCat.{max u v} R)
    [Module.Finite R M]
    (hM : IsZero ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).obj M)) :
    IsZero M := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  have hsub : Subsingleton ((R ⧸ I) ⊗[R] M) := ModuleCat.subsingleton_of_isZero hM
  have hquot : Subsingleton (M ⧸ I • (⊤ : Submodule R M)) :=
    e.toEquiv.surjective.subsingleton
  have htop : I • (⊤ : Submodule R M) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hquot
  have hz : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤
      (Module.Finite.fg_top) (by rw [htop]) hI
  have : Subsingleton M := by
    apply subsingleton_of_forall_eq 0
    intro x
    have hx : x ∈ (⊥ : Submodule R M) := hz ▸ Submodule.mem_top
    exact hx
  exact ModuleCat.isZero_of_subsingleton M

private lemma isStrictlyLE_of_quotient_extendScalars
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : ∀ i, Module.Finite R (P.X i)) (b : ℤ)
    [CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) b] :
    P.IsStrictlyLE b := by
  refine (CochainComplex.isStrictlyLE_iff P b).mpr fun i hi ↦ ?_
  have := hP i
  exact isZero_of_isZero_quotient_extendScalars I hI (P.X i) <|
    CochainComplex.isZero_of_isStrictlyLE
      (((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) b i hi

lemma exists_finiteFree_lift_representing_iso_with_bound
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I.IsLocallyNilpotent)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.Free (R ⧸ I) (E.X i))
    (e : DerivedCategory.Q.obj E ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (Ideal.Quotient.mk I)).functor.obj K)
    (hK : PseudoCoherence.IsPseudoCoherent K) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyLE b ∧
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk
        I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).comparison.app P ≫
          DerivedCategory.Q.map eRed.hom ≫ e.hom =
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk I)).functor.map eK.hom := by
  obtain ⟨P, hP, eRed, eK, he⟩ := exists_finiteFree_lift_representing_iso
    I K E ⟨⟨b, inferInstance⟩, hE⟩ e hK (fun x hx ↦ (hI x hx).isUnit_one_add)
  refine ⟨P, ?_, hP.finiteFree, eRed, eK, he⟩
  have hJac : I ≤ Ideal.jacobson ⊥ := fun x hx ↦
    Ideal.mem_jacobson_bot.mpr fun y ↦ (hI (x * y) (I.mul_mem_right y hx)).isUnit_add_one
  have : CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) b :=
    (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi ↦
      (CochainComplex.isZero_of_isStrictlyLE E b i hi).of_iso
        ((HomologicalComplex.eval _ _ i).mapIso eRed)
  exact isStrictlyLE_of_quotient_extendScalars I hJac P (fun i ↦ (hP.finiteFree i).1) b

/-- An additive adjunction induces the degreewise adjunction on complexes. -/
public def mapHomologicalComplexAdjunction
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit :=
    { app := fun X =>
        { f := fun n => adj.unit.app (X.X n)
          comm' := fun i j _ => by simp }
      naturality := fun X Y f => by ext n; simp }
  counit :=
    { app := fun Y =>
        { f := fun n => adj.counit.app (Y.X n)
          comm' := fun i j _ => by simp }
      naturality := fun X Y f => by ext n; simp }
  left_triangle_components := by intro X; ext n; simp
  right_triangle_components := by intro Y; ext n; simp

/-- An additive adjunction descends to the homotopy categories. -/
public def mapHomotopyCategoryAdjunction
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι) :
    F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit := Quotient.natTransLift _
    (Functor.whiskerRight (mapHomologicalComplexAdjunction adj c).unit
      (HomotopyCategory.quotient C c))
  counit := Quotient.natTransLift _
    (Functor.whiskerRight (mapHomologicalComplexAdjunction adj c).counit
      (HomotopyCategory.quotient D c))
  left_triangle_components := by
    rintro ⟨X⟩
    exact ((HomotopyCategory.quotient D c).map_comp _ _).symm.trans
      ((congrArg _ ((mapHomologicalComplexAdjunction adj c).left_triangle_components X)).trans
        ((HomotopyCategory.quotient D c).map_id _))
  right_triangle_components := by
    rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient C c).map_comp _ _).symm.trans
      ((congrArg _ ((mapHomologicalComplexAdjunction adj c).right_triangle_components Y)).trans
        ((HomotopyCategory.quotient C c).map_id _))

/-- Morphisms from a K-projective complex agree in the homotopy and derived categories. -/
public def derivedHomEquiv
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P E : CochainComplex C ℤ) [P.IsKProjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj E) ≃
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective P _)).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app P)
        ((DerivedCategory.quotientCompQhIso C).app E))

private lemma derivedHomEquiv_map
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P E : CochainComplex C ℤ) [P.IsKProjective] (f : P ⟶ E) :
    derivedHomEquiv P E ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  show (DerivedCategory.quotientCompQhIso C).inv.app P ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app E = _
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp

/-- The chain-level adjunction on derived morphisms out of a K-projective complex whose
extension is K-projective. -/
public def derivedAdjunctionHomEquiv
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex C ℤ) (E : CochainComplex D ℤ)
    [P.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)] :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj E) ≃
      (DerivedCategory.Q.obj P ⟶ G.mapDerivedCategory.obj (DerivedCategory.Q.obj E)) :=
  (derivedHomEquiv _ _).symm.trans
    (((mapHomotopyCategoryAdjunction adj (.up ℤ)).homEquiv _ _).trans
      ((derivedHomEquiv P _).trans
        (Iso.homCongr (Iso.refl _) (G.mapDerivedCategoryFactors.app E).symm)))

set_option backward.isDefEq.respectTransparency false in
lemma derivedAdjunctionHomEquiv_map
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex C ℤ) (E : CochainComplex D ℤ)
    [P.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)]
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ E) :
    derivedAdjunctionHomEquiv adj P E (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app E := by
  simp only [derivedAdjunctionHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  show (derivedHomEquiv P ((G.mapHomologicalComplex (.up ℤ)).obj E))
    ((mapHomotopyCategoryAdjunction adj (.up ℤ)).homEquiv _ _
      ((derivedHomEquiv ((F.mapHomologicalComplex (.up ℤ)).obj P) E).symm
        (DerivedCategory.Q.map f))) ≫ _ = _
  rw [← derivedHomEquiv_map _ _ f, Equiv.symm_apply_apply]
  show derivedHomEquiv _ _ ((HomotopyCategory.quotient _ _).map
    ((mapHomologicalComplexAdjunction adj (.up ℤ)).homEquiv _ _ f)) ≫ _ = _
  rw [derivedHomEquiv_map]
  rfl

lemma exists_chainMap_of_isKProjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P E : CochainComplex C ℤ) [P.IsKProjective]
    (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E) :
    ∃ f : P ⟶ E, DerivedCategory.Q.map f = g := by
  obtain ⟨a, ha⟩ := (derivedHomEquiv P E).surjective g
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective a
  exact ⟨f, (derivedHomEquiv_map P E f).symm.trans ha⟩

private lemma derivedAdjunctionHomEquiv_eq
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex C ℤ) (E : CochainComplex D ℤ)
    [P.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)]
    (g : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj E) :
    derivedAdjunctionHomEquiv adj P E g =
      DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map g := by
  obtain ⟨f, rfl⟩ := exists_chainMap_of_isKProjective _ _ g
  rw [derivedAdjunctionHomEquiv_map, Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact G.mapDerivedCategoryFactors.inv.naturality f

private lemma bijective_derived_unit_comp
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex C ℤ)
    [P.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)]
    (Y : DerivedCategory D) :
    Function.Bijective (fun g : DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶ Y ↦
      DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map g) := by
  let E := DerivedCategory.Q.objPreimage Y
  let e := DerivedCategory.Q.objObjPreimageIso Y
  let a := Iso.homCongr (Iso.refl (DerivedCategory.Q.obj
    ((F.mapHomologicalComplex (.up ℤ)).obj P))) e
  let b := Iso.homCongr (Iso.refl (DerivedCategory.Q.obj P))
    (G.mapDerivedCategory.mapIso e)
  let h := a.symm.trans ((derivedAdjunctionHomEquiv adj P E).trans b)
  have hh : (fun g : DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶ Y ↦
      DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map g) = h := by
    funext g
    dsimp only [h, Equiv.trans_apply]
    rw [derivedAdjunctionHomEquiv_eq]
    dsimp [a, b, Iso.homCongr]
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp,
      e.inv_hom_id, Category.comp_id]
  rw [hh]
  exact h.bijective

private lemma isIso_homEquiv_symm_of_bijective
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y : D} (u : X ⟶ G.obj Y)
    (hu : ∀ Z, Function.Bijective (fun g : Y ⟶ Z ↦ u ≫ G.map g)) :
    IsIso ((adj.homEquiv X Y).symm u) := by
  apply isIso_of_coyoneda_map_bijective
  intro Z
  have h := (adj.homEquiv X Z).symm.bijective.comp (hu Z)
  convert h using 1
  ext g
  exact (adj.homEquiv_naturality_right_symm u g).symm

/-- The derived transpose of a chain map is invertible exactly when its chain-level transpose
is a quasi-isomorphism. -/
public lemma isIso_derived_transpose_iff
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {FD : DerivedCategory C ⥤ DerivedCategory D}
    (adjD : FD ⊣ G.mapDerivedCategory) (P : CochainComplex C ℤ) (E : CochainComplex D ℤ)
    [P.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj P)]
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ E) :
    IsIso ((adjD.homEquiv _ _).symm
      (DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app E)) ↔ QuasiIso f := by
  let u := DerivedCategory.Q.map ((mapHomologicalComplexAdjunction adj (.up ℤ)).unit.app P) ≫
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have := isIso_homEquiv_symm_of_bijective adjD u (fun Y ↦ by
    simpa only [u, Category.assoc] using bijective_derived_unit_comp adj P Y)
  rw [← derivedAdjunctionHomEquiv_map, derivedAdjunctionHomEquiv_eq]
  rw [← Category.assoc]
  show IsIso ((adjD.homEquiv _ _).symm (u ≫ G.mapDerivedCategory.map
    (DerivedCategory.Q.map f))) ↔ _
  rw [Adjunction.homEquiv_naturality_right_symm, isIso_comp_left_iff]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso D f

/-- Two distinguished triangles with the same second map have isomorphic first terms, by an
isomorphism compatible with the maps into that second object. -/
lemma exists_iso_comp_eq_of_distinguished_mk
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K L P Q : C} (p : K ⟶ P) (q : L ⟶ P) (d : P ⟶ Q)
    (δ : Q ⟶ K⟦(1 : ℤ)⟧) (ε : Q ⟶ L⟦(1 : ℤ)⟧)
    (hK : Pretriangulated.Triangle.mk p d δ ∈ distTriang C)
    (hL : Pretriangulated.Triangle.mk q d ε ∈ distTriang C) :
    ∃ e : K ≅ L, e.hom ≫ q = p := by
  let T := Pretriangulated.Triangle.mk p d δ
  let U := Pretriangulated.Triangle.mk q d ε
  obtain ⟨a, ha, hδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T U hK hL (𝟙 P) (𝟙 Q) (by simp [T, U])
  let f : T ⟶ U :=
    { hom₁ := a
      hom₂ := 𝟙 P
      hom₃ := 𝟙 Q
      comm₁ := ha
      comm₂ := by simp [T, U]
      comm₃ := hδ }
  have : IsIso f.hom₁ := Pretriangulated.isIso₁_of_isIso₂₃ f hK hL
    (inferInstanceAs (IsIso (𝟙 P))) (inferInstanceAs (IsIso (𝟙 Q)))
  refine ⟨asIso f.hom₁, ?_⟩
  show a ≫ q = p
  change p ≫ 𝟙 P = a ≫ q at ha
  simpa only [Category.comp_id] using ha.symm

end StacksDraft.DerivedInverseLimit

end
