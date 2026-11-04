module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Util.CountHeartbeats
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.Colimit
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Restriction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFiniteType05MF
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.HenselianCollapse
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.TFAE
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties

/-!
# Localization and associated-point lemmas for the filtered-colimit presentation

Auxiliary results for the filtered-colimit presentation of Stacks 05U7: transport of
flatness and freeness along ring equivalences, a finite `B`-module as the localization of a
finite submodule over a finite type subalgebra, and the finiteness and specialization of the
associated points of the closed fibre.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u v uM uP uQ uN w

/-- The stalk of `Spec A` at the closed point of a local ring `A` is a local ring. This is the
instance of `AlgebraicGeometry.Scheme` for a point of the scheme, which instance search does not
reach when the point is written as `IsLocalRing.closedPoint A`: the coercion of
`IsLocalRing.closedPoint A` to a point of `Spec A` is not inserted while the class is being
elaborated. -/
private instance isLocalRing_stalk_closedPoint (A : CommRingCat.{u}) [IsLocalRing A] :
    IsLocalRing ((Spec A).presheaf.stalk (closedPoint A)) :=
  let x : Spec A := closedPoint A
  inferInstanceAs (IsLocalRing ((Spec A).presheaf.stalk x))

private lemma isIso_pullbackMap_of_isIso {D : Type*} [Category.{w} D] {W X Y Z S T : D}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    (h₁ : IsIso i₁) (h₂ : IsIso i₂) (h₃ : IsIso i₃) :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  let := h₁
  let := h₂
  let := h₃
  infer_instance

private noncomputable def restrictScalarsOfTowers {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module A M] [Module A N]
    (hM : IsScalarTower A R M) (hN : IsScalarTower A R N) (e : M ≃ₗ[R] N) :
    M ≃ₗ[A] N :=
  letI := hM
  letI := hN
  e.restrictScalars A

private lemma free_of_henselian_scalar_equiv
    {A : Type u} {R' : Type v} {M : Type w}
    [CommRing A] [CommRing R'] [Algebra A R']
    [AddCommGroup M] [Module A M] [Module R' M] [IsScalarTower A R' M]
    (e : R' ≃ₐ[A] A) [Module.Free R' M] : Module.Free A M := by
  let σ : R' →+* A := e.toRingHom
  let σ' : A →+* R' := e.symm.toRingHom
  let : RingHomInvPair σ σ' := ⟨by ext r; simp [σ, σ'], by ext a; simp [σ, σ']⟩
  let : RingHomInvPair σ' σ := ⟨by ext a; simp [σ, σ'], by ext r; simp [σ, σ']⟩
  have hmap (r : R') : algebraMap A R' (e r) = r := by
    apply e.injective
    simp
  let eM : M ≃ₛₗ[σ] M := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r m
      calc
        r • m = algebraMap A R' (e r) • m :=
          congrArg (fun t : R' => t • m) (hmap r).symm
        _ = (e r) • m := algebraMap_smul (R := A) (A := R') (e r) m
  }
  exact Module.Free.of_equiv eM

private lemma flat_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    (hsmul : ∀ (s : S) (m : M), s • m = e.symm s • m)
    [Module.Flat R M] [Small.{v} S] : Module.Flat S M := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m => by
    show e r • m = r • m
    simpa using hsmul (e r) m
  have : IsScalarTower S R M :=
    IsScalarTower.of_algebraMap_smul fun s m => (hsmul s m).symm
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let : Module R N := Module.compHom N e.toRingHom
  let : Module R P := Module.compHom P e.toRingHom
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S R N := IsScalarTower.of_algebraMap_smul fun s n => by
    show e (e.symm s) • n = s • n
    simp
  have : IsScalarTower S R P := IsScalarTower.of_algebraMap_smul fun s p => by
    show e (e.symm s) • p = s • p
    simp
  let fR : N →ₗ[R] P := f.restrictScalars R
  have hflat := Module.Flat.rTensor_preserves_injective_linearMap (M := M) fR hf
  let dN : (N ⊗[S] M) ≃ₗ[S] (N ⊗[R] M) :=
    TensorProduct.equivOfCompatibleSMul R S S N M
  let dP : (P ⊗[S] M) ≃ₗ[S] (P ⊗[R] M) :=
    TensorProduct.equivOfCompatibleSMul R S S P M
  have hcomm (z : N ⊗[S] M) : dP ((f.rTensor M) z) = (fR.rTensor M) (dN z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul n m => rfl
  intro x y hxy
  exact dN.injective (hflat ((hcomm x).symm.trans ((congrArg dP hxy).trans (hcomm y))))

private lemma isUnit_algebraMap_end_of_isUnit_algebraMap
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (r : R) (hr : IsUnit (algebraMap R S r)) :
    IsUnit (algebraMap R (Module.End R M) r) := by
  let μ : S →+* Module.End R M := {
    toFun := fun s => {
      toFun := fun m => s • m
      map_add' := fun x y => smul_add s x y
      map_smul' := fun a m => calc
        s • (a • m) = s • (algebraMap R S a • m) := by rw [algebraMap_smul]
        _ = algebraMap R S a • (s • m) := smul_comm _ _ _
        _ = a • (s • m) := by rw [algebraMap_smul]
    }
    map_one' := by ext m; simp
    map_mul' := fun a b => by ext m; exact (smul_smul a b m).symm
    map_zero' := by ext m; simp
    map_add' := fun a b => by ext m; exact add_smul a b m
  }
  have heq : algebraMap R (Module.End R M) r = μ (algebraMap R S r) := by
    ext m
    show r • m = algebraMap R S r • m
    exact (IsScalarTower.algebraMap_smul (R := R) (A := S) r m).symm
  rw [heq]
  exact hr.map μ

private lemma bijective_smul_of_isUnit_algebraMap
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (r : R) (hr : IsUnit (algebraMap R S r)) :
    Function.Bijective (fun m : M => r • m) := by
  exact (Module.End.isUnit_iff _).1 (isUnit_algebraMap_end_of_isUnit_algebraMap r hr)

private lemma exists_finite_submodule_spanning_module
    {R S : Type*} {M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] :
    ∃ (M₀ : Submodule R M), Module.Finite R M₀ ∧
      Submodule.span S (M₀ : Set M) = ⊤ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := M)
  let M₀ : Submodule R M := Submodule.span R (Set.range s)
  refine ⟨M₀, Module.Finite.span_of_finite R (Set.finite_range s), ?_⟩
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono Submodule.subset_span

private lemma localized_submodule_of_spanning
    {R S M : Type*} [CommRing R] [CommRing S] {T : Submonoid R}
    [Algebra R S] [IsLocalization T S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (M₀ : Submodule R M)
    (hspan : Submodule.span S (M₀ : Set M) = ⊤) :
    IsLocalizedModule T (M₀.subtype : M₀ →ₗ[R] M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact fun t => isUnit_algebraMap_end_of_isUnit_algebraMap (S := S) (t : R)
      (IsLocalization.map_units S t)
  · intro x
    have hx : x ∈ Submodule.span S (M₀ : Set M) := hspan ▸ Submodule.mem_top
    have hP : ∀ y ∈ Submodule.span S (M₀ : Set M),
        ∃ t : T, ∃ m : M₀, (t : R) • y = (m : M) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => exact ⟨1, ⟨z, hz⟩, by simp⟩
      | zero => exact ⟨1, 0, by simp⟩
      | add y z _ _ hy hz =>
          obtain ⟨t, m, hm⟩ := hy
          obtain ⟨u, n, hn⟩ := hz
          refine ⟨u * t, ⟨(u : R) • m + (t : R) • n, ?_⟩, ?_⟩
          · exact add_mem (M₀.smul_mem _ m.2) (M₀.smul_mem _ n.2)
          · show ((u : R) * (t : R)) • (y + z) = _
            rw [mul_smul, smul_add, smul_add, hm]
            rw [smul_comm (u : R) (t : R) z, hn]
      | smul a y _ hy =>
          obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj T a
          obtain ⟨u, m, hm⟩ := hy
          refine ⟨t * u, ⟨(b : R) • m, M₀.smul_mem _ m.2⟩, ?_⟩
          show ((t * u : T) : R) • (a • y) = _
          calc
            ((t * u : T) : R) • (a • y) =
                algebraMap R S ((t : R) * (u : R)) • (a • y) := by
              simpa only [Submonoid.coe_mul] using
                (IsScalarTower.algebraMap_smul (R := R) (A := S)
                  ((t : R) * (u : R)) (a • y)).symm
            _ =
                (algebraMap R S ((t : R) * (u : R)) * a) • y := by rw [mul_smul]
            _ = (algebraMap R S b * algebraMap R S (u : R)) • y := by
              congr 1
              rw [map_mul]
              calc
                (algebraMap R S (t : R) * algebraMap R S (u : R)) * a =
                    (a * algebraMap R S (t : R)) * algebraMap R S (u : R) := by ring
                _ = algebraMap R S b * algebraMap R S (u : R) := by rw [hbt]
            _ = algebraMap R S b • (algebraMap R S (u : R) • y) := by rw [mul_smul]
            _ = algebraMap R S b • m := by
              rw [IsScalarTower.algebraMap_smul (R := R) (A := S) (u : R) y, hm]
            _ = (b : R) • (m : M) :=
              IsScalarTower.algebraMap_smul (R := R) (A := S) b (m : M)
    obtain ⟨t, m, hm⟩ := hP x hx
    exact ⟨⟨m, t⟩, hm⟩
  · intro x y hxy
    exact ⟨1, by simp [Submodule.subtype_injective M₀ hxy]⟩

private lemma localizedModule_of_localUnits
    {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] {S : Submonoid R} (P : Ideal R) [P.IsPrime]
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (hS : S ≤ P.primeCompl)
    (hunit : ∀ r : P.primeCompl, Function.Bijective (fun m : M' => (r : R) • m)) :
    IsLocalizedModule P.primeCompl f := by
  refine ⟨fun r => (Module.End.isUnit_iff _).2 (hunit r), ?_, ?_⟩
  · intro y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨s, hS s.2⟩⟩, hs⟩
  · intro x y hxy
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) hxy
    exact ⟨⟨s, hS s.2⟩, hs⟩

private lemma isLocalizedModule_of_bijective_smul
    {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (S : Submonoid R) (f : M →ₗ[R] M')
    (hunit : ∀ r : S, Function.Bijective (fun m : M' => (r : R) • m))
    (hsurj : ∀ y : M', ∃ x : M × S, (x.2 : R) • y = f x.1)
    (hexists : ∀ x₁ x₂ : M, f x₁ = f x₂ → ∃ c : S, (c : R) • x₁ = (c : R) • x₂) :
    IsLocalizedModule S f :=
  ⟨fun r => (Module.End.isUnit_iff _).2 (hunit r), hsurj, fun {x₁ x₂} h => hexists x₁ x₂ h⟩

private lemma mapQ_injective_of_preimage
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Submodule R M) (J : Submodule R N) (f : M →ₗ[R] N)
    (hI : I ≤ J.comap f)
    (hpre : ∀ x, f x ∈ J → x ∈ I) :
    Function.Injective (Submodule.mapQ I J f hI) := by
  have hEq : J.comap f = I := le_antisymm (fun x hx => hpre x hx) hI
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hEq, Submodule.mkQ_map_self]

private lemma maximalIdeal_smul_top_restrictScalars_of_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hsurj : Function.Surjective (algebraMap R S)) :
    (maximalIdeal S • (⊤ : Submodule S M)).restrictScalars R =
      maximalIdeal R • (⊤ : Submodule R M) := by
  ext m
  constructor
  · intro hm
    change m ∈ maximalIdeal S • (⊤ : Submodule S M) at hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro s hs n hn
      obtain ⟨r, rfl⟩ := hsurj s
      rw [IsScalarTower.algebraMap_smul]
      apply Submodule.smul_mem_smul _ (Submodule.mem_top)
      rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]
      exact hs
    · exact fun x y hx hy => Submodule.add_mem _ hx hy
  · intro hm
    show m ∈ maximalIdeal S • (⊤ : Submodule S M)
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr n hn
      rw [← IsScalarTower.algebraMap_smul S r n]
      apply Submodule.smul_mem_smul _ (Submodule.mem_top)
      show r ∈ (maximalIdeal S).comap (algebraMap R S)
      rw [IsLocalRing.maximalIdeal_comap]
      exact hr
    · exact fun x y hx hy => Submodule.add_mem _ hx hy

private lemma injective_mapQ_restrictScalars_of_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hsurj : Function.Surjective (algebraMap R S)) (f : M →ₗ[S] M)
    (hf : Function.Injective (Submodule.mapQ
      (maximalIdeal S • (⊤ : Submodule S M)) (maximalIdeal S • (⊤ : Submodule S M))
      f (Submodule.smul_top_le_comap_smul_top (maximalIdeal S) f))) :
    Function.Injective (Submodule.mapQ
      (maximalIdeal R • (⊤ : Submodule R M)) (maximalIdeal R • (⊤ : Submodule R M))
      (f.restrictScalars R)
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (f.restrictScalars R))) := by
  apply mapQ_injective_of_preimage
  intro m hm
  have heq := maximalIdeal_smul_top_restrictScalars_of_surjective (M := M) hsurj
  rw [← heq] at hm ⊢
  change f m ∈ maximalIdeal S • (⊤ : Submodule S M) at hm
  show m ∈ maximalIdeal S • (⊤ : Submodule S M)
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hf
  simpa using (Submodule.Quotient.mk_eq_zero
    (maximalIdeal S • (⊤ : Submodule S M))).mpr hm

private lemma exists_open_mem_avoiding_finite_specializations {X : Type*}
    [TopologicalSpace X] (x : X) (E : Set X) (hE : E.Finite)
    (hbad : ∀ y ∈ E, ¬ y ⤳ x) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y ∈ E, y ∉ U := by
  classical
  refine Set.Finite.induction_on
    (motive := fun E _ => (∀ y ∈ E, ¬ y ⤳ x) →
      ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ ∀ y ∈ E, y ∉ U)
    E hE ?_ ?_ hbad
  · intro _
    exact ⟨⊤, by simp, by simp⟩
  · intro a s ha hs ih hbad
    obtain ⟨U, hxU, havoid⟩ := ih (by
      intro y hy
      apply hbad y
      simp [hy])
    let V : TopologicalSpace.Opens X := ⟨{z | z ∉ closure ({a} : Set X)},
      isOpen_compl_iff.mpr isClosed_closure⟩
    have hxV : x ∈ V := by
      show x ∉ closure ({a} : Set X)
      intro hxcl
      apply hbad a (by simp)
      exact (specializes_iff_mem_closure).mpr hxcl
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff] at hy
    rcases hy with rfl | hy
    · exact fun h => h.2 (subset_closure (Set.mem_singleton y))
    · exact fun h => havoid y hy h.1

/-- The fibre of a morphism locally of finite type is locally Noetherian. -/
private lemma isLocallyNoetherian_fiber {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) : IsLocallyNoetherian (f.fiber s) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)

private theorem associatedPoints_fiber_finite
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    (Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite := by
  have := isLocallyNoetherian_fiber f s
  let G := (Scheme.Modules.pullback (f.fiberι s)).obj F
  let : G.IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
      (f.fiber s).toRingedSpace X.toRingedSpace (f.fiberι s).toLRSHom.toShHom F
      (inferInstanceAs F.IsQuasicoherent)
  let : G.IsFiniteType :=
    @AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (f.fiber s).toRingedSpace X.toRingedSpace (f.fiberι s).toLRSHom.toShHom F
      (inferInstanceAs F.IsFiniteType)
  let : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType G
  have h := AlgebraicGeometry.associatedPoints_inter_finite G ⊤ isCompact_univ
  simpa using h

private lemma associatedPoints_pullback_iff_of_etale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (F : Y.Modules) [F.IsQuasicoherent] (x : X) :
    x ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback g).obj F) ↔
      g x ∈ Stacks.Divisors.associatedPoints F := by
  rw [AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints X,
    AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints Y]
  simpa only [Stacks.Divisors.mem_weaklyAssociatedPoints_iff] using
    (AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_etale g F x)

private lemma associatedPrimeStacks_subset_of_injective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (hφ : Function.Injective φ)
    {p : Ideal R} (hp : IsAssociatedPrimeStacks R M p) :
    IsAssociatedPrimeStacks R N p := by
  rcases hp with ⟨hp, m, hm⟩
  refine ⟨hp, φ m, ?_⟩
  ext r
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← map_smul,
    map_eq_zero_iff φ hφ]
  rw [← hm, Submodule.mem_colon_span_singleton]; simp only [Submodule.mem_bot]

private alias associatedPoints_subset_of_iso :=
    AlgebraicGeometry.associatedPoints_subset_of_moduleIso

/-- Alias of `AlgebraicGeometry.associatedPoints_eq_of_moduleIso`. -/
private alias associatedPoints_eq_of_iso := AlgebraicGeometry.associatedPoints_eq_of_moduleIso

private noncomputable def fiberModuleIso {A B S : Scheme.{u}}
    (i : A ⟶ B) (f : B ⟶ S) (F : B.Modules) (s : S) :
    ((Scheme.Modules.pullback (fiberMapOfSourceHom i f s)).obj
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≅
      ((Scheme.Modules.pullback ((i ≫ f).fiberι s)).obj
        ((Scheme.Modules.pullback i).obj F)) := by
  have hmap : fiberMapOfSourceHom i f s ≫ f.fiberι s =
      (i ≫ f).fiberι s ≫ i := fiberMapOfSourceHom_fiberι i f s
  exact (Scheme.Modules.pullbackComp (fiberMapOfSourceHom i f s) (f.fiberι s)).app F ≪≫
    (Scheme.Modules.pullbackCongr hmap).app F ≪≫
      ((Scheme.Modules.pullbackComp ((i ≫ f).fiberι s) i).app F).symm

private lemma associatedPoints_fiber_specialize_of_openImmersion
    {Z X S : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent]
    (s : S) (x : Z)
    (hgen : ∀ y ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι s)).obj F), (f.fiberι s y) ⤳ j x) :
    ∀ z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback ((j ≫ f).fiberι s)).obj
        ((Scheme.Modules.pullback j).obj F)), ((j ≫ f).fiberι s z) ⤳ x := by
  let m := fiberMapOfSourceHom j f s
  let G := (Scheme.Modules.pullback (f.fiberι s)).obj F
  have : G.IsQuasicoherent := AlgebraicGeometry.pullback_isQuasicoherent' (f.fiberι s) F
  have := isLocallyNoetherian_fiber f s
  have := isLocallyNoetherian_fiber (j ≫ f) s
  have : Etale m := MorphismProperty.of_isPullback
    (fiberMapOfSourceHom_isPullback j f s).flip inferInstance
  intro z hz
  have hz' : z ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback m).obj G) :=
    (associatedPoints_eq_of_iso (fiberModuleIso j f F s)).symm ▸ hz
  have h := hgen (m z) ((associatedPoints_pullback_iff_of_etale m G z).mp hz')
  apply j.isOpenEmbedding.isInducing.specializes_iff.mp
  have he : f.fiberι s (m z) = j ((j ≫ f).fiberι s z) :=
    congrArg (fun k : (j ≫ f).fiber s ⟶ X => k z)
      (fiberMapOfSourceHom_fiberι j f s)
  rwa [← he]

private lemma germ_injective_of_associatedPoints_specialize
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (hgen : ∀ y ∈ Stacks.Divisors.associatedPoints F, y ⤳ x) :
    Function.Injective ((F.presheaf.germ ⊤ x (by simp)).hom) := by
  intro s t hst
  obtain ⟨W, hxW, iWtop, jWtop, heq⟩ :=
    F.presheaf.germ_eq x (by simp) (by simp) s t hst
  have hass : Stacks.Divisors.associatedPoints F ⊆ (W : Set X) :=
    fun y hy => (hgen y hy).mem_open W.isOpen hxW
  have heq' :
      (F.presheaf.map (homOfLE (show W ≤ (⊤ : X.Opens) from le_top)).op).hom s =
        (F.presheaf.map (homOfLE (show W ≤ (⊤ : X.Opens) from le_top)).op).hom t := by
    convert heq using 1 <;> congr 2
  exact AlgebraicGeometry.restriction_injective_of_associatedPoints_subset X F W hass heq'

private lemma fiber_sections_smul_injective
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    [IsLocallyNoetherian (f.fiber s)] (G : (f.fiber s).Modules) [G.IsQuasicoherent]
    (x : X) (hx : f x = s)
    (hgen : ∀ y ∈ Stacks.Divisors.associatedPoints G, (f.fiberι s y) ⤳ x)
    (r : Γ(X, ⊤)) (hr : IsUnit (X.presheaf.germ ⊤ x (by simp) r)) :
    Function.Injective (fun m : Γ(G, ⊤) => (f.fiberι s).appTop r • m) := by
  obtain ⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s) := by
    rw [f.range_fiberι]
    exact hx
  have hginj := germ_injective_of_associatedPoints_specialize G y fun z hz =>
    (f.fiberι s).isEmbedding.isInducing.specializes_iff.mp (hgen z hz)
  let : Module ((f.fiber s).presheaf.stalk y) (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (f.fiber s).presheaf) G.val y
  have hu : IsUnit ((f.fiber s).presheaf.germ ⊤ y (by simp)
      ((f.fiberι s).appTop r)) := by
    have h : IsUnit ((X.presheaf.germ ⊤ (f.fiberι s y) (by simp) ≫
        (f.fiberι s).stalkMap y).hom r) := hr.map ((f.fiberι s).stalkMap y).hom
    rw [Scheme.Hom.germ_stalkMap] at h
    exact h
  intro a b hab
  apply hginj
  apply hu.smul_bijective.injective
  have hh := congrArg (fun m => G.presheaf.germ ⊤ y (by simp) m) hab
  exact (G.val.germ_smul y ⊤ (by simp) ((f.fiberι s).appTop r) a).symm.trans
    (hh.trans (G.val.germ_smul y ⊤ (by simp) ((f.fiberι s).appTop r) b))

end
