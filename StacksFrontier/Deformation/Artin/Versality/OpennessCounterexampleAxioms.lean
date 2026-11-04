module

public import StacksFrontier.Deformation.Artin.Versality.OpennessCounterexample
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# Axioms [0]–[3] for the openness-of-versality example

Tag 07XR builds, over `S = Spec k[s, t]`, the full subcategory `𝒳` of the big fppf site on
the schemes admitting an affine open covering whose coordinate rings `A` satisfy
`A = (s, t, f_1, …, f_n)` with `f_i s = 0`, and asserts that `𝒳` satisfies the axioms
[0]–[4] of Artin's axioms while failing openness of versality. This file proves axioms [0]–[3]:
`𝒳` is a stack in groupoids, it is limit preserving, it satisfies condition (RS), and the
tangent spaces and infinitesimal automorphism spaces of its predeformation categories are
finite dimensional.

## Main definitions

* `Deformation.Artin.OpennessCounterexample.stalkAlgebra`,
  `Deformation.Artin.OpennessCounterexample.sectionsAlgebra` — the
  `k[s,t]`-algebra structures on the stalks and on the global sections of a scheme over
  `Spec k[s,t]`.
* `Deformation.Artin.artinAxiomsCFG` — `𝒳` as a category fibred in groupoids over the big fppf
  site.

## Main results

* `Deformation.Artin.isArtinAxiomsObject_iff_forall_stalk` — an object lies in `𝒳` exactly
  when its stalks satisfy the condition.
* `Deformation.Artin.isArtinAxiomsObject_of_mem_topology` — the condition is fppf local.
* `Deformation.Artin.isFiberedInGroupoids_artinAxiomsCategory` — `𝒳` is fibred in groupoids.
* `Deformation.Artin.isStackInGroupoids_artinAxiomsCategory` — `𝒳` is a stack in groupoids for
  the fppf topology, axiom [0].
* `Deformation.Artin.isLimitPreserving_artinAxiomsCategory` — axiom [1]: `𝒳` is limit
  preserving.
* `Deformation.Artin.satisfiesRS_artinAxiomsCategory` — axiom [2]: `𝒳` satisfies
  condition (RS).
* `Deformation.Artin.finiteDimensional_tangentSpace_infinitesimalAutomorphisms_artinAxiomsCategory`
  — the tangent and infinitesimal automorphism spaces are finite dimensional, axiom [3].

## References

* [Stacks Project, Tag 07XR](https://stacks.math.columbia.edu/tag/07XR)
* [Stacks Project, Tag 07XJ](https://stacks.math.columbia.edu/tag/07XJ)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))

/-! ### Admissibility of a local algebra -/

/-- A local algebra is admissible exactly when `s` vanishes as soon as `s` and `t` both lie
in the maximal ideal. -/
public theorem isAdmissible_iff_of_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra (MvPolynomial (Fin 2) k) A] :
    IsAdmissible k A ↔
      (algebraMap (MvPolynomial (Fin 2) k) A (X 0) ∈ IsLocalRing.maximalIdeal A →
        algebraMap (MvPolynomial (Fin 2) k) A (X 1) ∈ IsLocalRing.maximalIdeal A →
          algebraMap (MvPolynomial (Fin 2) k) A (X 0) = 0) := by
  refine ⟨fun h hs ht => eq_zero_of_isAdmissible A hs ht h, fun h => ?_⟩
  by_cases hs : algebraMap (MvPolynomial (Fin 2) k) A (X 0) ∈ IsLocalRing.maximalIdeal A
  · by_cases ht : algebraMap (MvPolynomial (Fin 2) k) A (X 1) ∈ IsLocalRing.maximalIdeal A
    · exact isAdmissible_of_eq_zero A (h hs ht)
    · obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.mp ht
      refine ⟨0, Fin.elim0, 0, ↑v⁻¹, Fin.elim0, ?_, fun i => i.elim0⟩
      simp [← hv]
  · obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.mp hs
    refine ⟨0, Fin.elim0, ↑v⁻¹, 0, Fin.elim0, ?_, fun i => i.elim0⟩
    simp [← hv]

/-! ### The condition on stalks -/

/-- The `k[s,t]`-algebra structure on a stalk of a scheme over `Spec k[s,t]`. -/
@[instance_reducible]
public def OpennessCounterexample.stalkAlgebra {T : Scheme.{u}}
    (τ : T ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x : T) :
    Algebra (MvPolynomial (Fin 2) k) (T.presheaf.stalk x) :=
  (AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ τ.appTop ≫
    T.presheaf.Γgerm x).hom.toAlgebra

/-- The map of stalks induced by a morphism of schemes over `Spec k[s,t]` is a map of
`k[s,t]`-algebras. -/
public theorem OpennessCounterexample.stalkMap_algebraMap_stalkAlgebra {T T' : Scheme.{u}}
    (g : T' ⟶ T)
    (τ : T ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x : T') (r : MvPolynomial (Fin 2) k) :
    g.stalkMap x (@algebraMap _ _ _ _ (OpennessCounterexample.stalkAlgebra τ (g x)) r) =
      @algebraMap _ _ _ _ (OpennessCounterexample.stalkAlgebra (g ≫ τ) x) r := by
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.germ_stalkMap g ⊤ x True.intro))
    ((AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ τ.appTop).hom r)).trans ?_
  change _ = (T'.presheaf.Γgerm x) ((g ≫ τ).appTop _)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Admissibility of stalks passes along a morphism of schemes over `Spec k[s,t]`. -/
public theorem isAdmissible_stalk_of_hom {T T' : Scheme.{u}} (g : T' ⟶ T)
    (τ : T ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x : T')
    (h : @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra τ (g x))) :
    @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra (g ≫ τ) x) :=
  isAdmissible_of_ringHom _ _ (g.stalkMap x).hom
    (OpennessCounterexample.stalkMap_algebraMap_stalkAlgebra g τ x) h

/-- Along an open immersion, admissibility of a stalk descends. -/
public theorem isAdmissible_stalk_of_isOpenImmersion {T T' : Scheme.{u}} (g : T' ⟶ T)
    [IsOpenImmersion g] (τ : T ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x : T')
    (h : @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra (g ≫ τ) x)) :
    @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra τ (g x)) := by
  refine isAdmissible_of_ringHom _ _ (inv (g.stalkMap x)).hom (fun r => ?_) h
  rw [← OpennessCounterexample.stalkMap_algebraMap_stalkAlgebra g τ x r]
  change (g.stalkMap x ≫ inv (g.stalkMap x)).hom _ = _
  rw [IsIso.hom_inv_id]
  rfl

/-- If every stalk of `Spec R` is admissible, so are the global sections of `Spec R`. -/
public theorem isAdmissible_sections_of_stalk (R : CommRingCat.{u})
    (σ : Spec R ⟶ Spec (.of (MvPolynomial (Fin 2) k)))
    (h : ∀ x : Spec R, @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra σ x)) :
    @IsAdmissible k _ Γ(Spec R, ⊤) _
      ((AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ σ.appTop).hom.toAlgebra) := by
  classical
  let := fun x : Spec R => StructureSheaf.stalkAlgebra R x
  let e := Scheme.ΓSpecIso R
  let φ : MvPolynomial (Fin 2) k →+* Γ(Spec R, ⊤) :=
    (AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ σ.appTop).hom
  let sR : R := e.hom (φ (X 0))
  let tR : R := e.hom (φ (X 1))
  let I : Ideal R := Ideal.span {sR, tR} ⊔ (Submodule.span R ({sR} : Set R)).annihilator
  have hgerm : ∀ (x : Spec R) (r : MvPolynomial (Fin 2) k),
      @algebraMap _ _ _ _ (OpennessCounterexample.stalkAlgebra σ x) r =
        algebraMap R ((Spec.structureSheaf R).presheaf.stalk x) (e.hom (φ r)) := by
    intro x r
    change (Spec R).presheaf.Γgerm x (φ r) = StructureSheaf.toStalk R x (e.hom (φ r))
    rw [← StructureSheaf.algebraMap_germ ⊤ x True.intro]
    change _ = (Spec R).presheaf.Γgerm x (e.inv (e.hom (φ r)))
    rw [Iso.hom_inv_id_apply]
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    let x : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
    have hloc := StructureSheaf.IsLocalization.to_stalk R x
    have hs : sR ∈ m := hIm (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
    have ht : tR ∈ m := hIm (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
    have hadm := (@isAdmissible_iff_of_isLocalRing k _ _ _ _
      (OpennessCounterexample.stalkAlgebra σ x)).mp (h x)
    rw [hgerm, hgerm] at hadm
    let St := (Spec.structureSheaf R).presheaf.stalk x
    obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff x.asIdeal.primeCompl St sR).mp
      (hadm ((IsLocalization.AtPrime.to_map_mem_maximal_iff St x.asIdeal sR).mpr hs)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff St x.asIdeal tR).mpr ht))
    exact u.2 (hIm (Ideal.mem_sup_right
      (by rwa [Submodule.mem_annihilator_span_singleton, smul_eq_mul])))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ I)
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hy
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hz
  have hφ : ∀ r, e.inv (e.hom (φ r)) = φ r := fun r => Iso.hom_inv_id_apply e (φ r)
  refine ⟨1, fun _ => e.inv z, e.inv a, e.inv b, fun _ => 1, ?_, fun _ => ?_⟩
  · change φ (X 0) * e.inv a + φ (X 1) * e.inv b + ∑ _ : Fin 1, e.inv z * 1 = 1
    rw [← hφ (X 0), ← hφ (X 1)]
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, ← map_mul, ← map_add]
    rw [mul_comm sR a, mul_comm tR b, hab, hyz, map_one]
  · change e.inv z * φ (X 0) = 0
    rw [← hφ (X 0), ← map_mul, hz, map_zero]

/-! ### The objects of the category, stalk by stalk -/

/-- An object satisfies `IsArtinAxiomsObject` exactly when its stalks are admissible. -/
public theorem isArtinAxiomsObject_iff_forall_stalk
    (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) :
    IsArtinAxiomsObject k B hS T ↔
      ∀ x, @IsAdmissible k _ _ _
        (OpennessCounterexample.stalkAlgebra (B.inclusion.map T.hom) x) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩ x
    obtain ⟨w, hw⟩ := 𝒰.covers x
    have h₁ : @IsAdmissible k _ _ _
        (OpennessCounterexample.stalkAlgebra (𝒰.f (𝒰.idx x) ≫ B.inclusion.map T.hom) w) :=
      isAdmissible_of_ringHom _ _ ((Spec (𝒰.X (𝒰.idx x))).presheaf.Γgerm w).hom
        (fun r => rfl) (h𝒰 (𝒰.idx x))
    have h₂ := isAdmissible_stalk_of_isOpenImmersion _ _ w h₁
    rwa [hw] at h₂
  · exact fun h => ⟨((BigFppfOver.toScheme B _ hS).obj T).affineOpenCover, fun _ =>
      isAdmissible_sections_of_stalk _ _ fun w => isAdmissible_stalk_of_hom _ _ w (h _)⟩

/-- A morphism of objects over `Spec k[s,t]` is compatible with their structure morphisms. -/
private theorem toScheme_map_comp_inclusion_map_hom
    {T T' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} (g : T' ⟶ T) :
    (BigFppfOver.toScheme B _ hS).map g ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))

/-- The condition `IsArtinAxiomsObject` is inherited along morphisms over `Spec k[s,t]`. -/
public theorem IsArtinAxiomsObject.of_hom
    {T T' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} (g : T' ⟶ T)
    (hT : IsArtinAxiomsObject k B hS T) : IsArtinAxiomsObject k B hS T' := by
  rw [isArtinAxiomsObject_iff_forall_stalk] at hT ⊢
  intro x
  have h := isAdmissible_stalk_of_hom ((BigFppfOver.toScheme B _ hS).map g)
    (B.inclusion.map T.hom) x (hT _)
  rwa [toScheme_map_comp_inclusion_map_hom] at h

/-- The inclusion of the full subcategory `IsArtinAxiomsObject` is fibred in groupoids over the
big fppf site of `Spec k[s,t]`. -/
public theorem isFiberedInGroupoids_artinAxiomsCategory :
    (ObjectProperty.ι (IsArtinAxiomsObject k B hS)).IsFiberedInGroupoids where
  exists_lift f x hx := by
    cases hx
    refine ⟨⟨_, x.property.of_hom B hS f⟩, ObjectProperty.homMk f, ?_⟩
    exact Functor.IsHomLift.map (p := ObjectProperty.ι (IsArtinAxiomsObject k B hS))
      (ObjectProperty.homMk (P := IsArtinAxiomsObject k B hS)
        (X := ⟨_, x.property.of_hom B hS f⟩) f)
  unique_lift φ ψ f h := by
    refine ⟨ObjectProperty.homMk f, ⟨rfl, ?_⟩, fun χ hχ => ?_⟩ <;> ext1
    exacts [h, hχ.1]

/-! ### Fibred categories whose fibres have at most one object -/

section ThinFibres

variable {C : Type*} [Category C] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ C)

/-- If `p` is injective on objects, each fibre has at most one object. -/
public theorem subsingleton_fiber_of_injective (hobj : Function.Injective p.obj)
    (U : C) : Subsingleton (p.Fiber U) :=
  ⟨fun a b => Subtype.ext (hobj (a.2.trans b.2.symm))⟩

/-- If `p` is faithful, each fibre is thin. -/
public theorem subsingleton_fiber_hom_of_faithful [p.Faithful] {U : C}
    (a b : p.Fiber U) : Subsingleton (a ⟶ b) := by
  refine ⟨fun φ ψ => Functor.Fiber.hom_ext (p.map_injective ?_)⟩
  have := φ.2
  have := ψ.2
  change p.map φ.1 = p.map ψ.1
  rw [IsHomLift.fac' p (𝟙 U) φ.1, IsHomLift.fac' p (𝟙 U) ψ.1]

/-- **Condition (RS) for a category whose fibres have at most one object.** When `p` is
faithful and injective on objects, the comparison from the fibre over `Z` to the two-fibre
product of the fibres over the other corners of a commutative square is an equivalence as
soon as the fibre over `Z` is inhabited whenever the fibres over `V` and `W` are. -/
public theorem isEquivalence_fiberSquareComparison_of_injective [p.Faithful]
    (hobj : Function.Injective p.obj) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hZ : p.Fiber V → p.Fiber W → p.Fiber Z) :
    (fiberSquareComparison p c f g i j h).IsEquivalence := by
  have hsub := subsingleton_fiber_of_injective p hobj
  have hhom := fun {T : C} (a b : p.Fiber T) => subsingleton_fiber_hom_of_faithful p a b
  let F := fiberSquareComparison p c f g i j h
  have hpb : ∀ {x y : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g)}
      (φ ψ : x ⟶ y), φ = ψ := fun φ ψ =>
    CategoricalPullback.hom_ext ((hhom _ _).elim _ _) ((hhom _ _).elim _ _)
  have : F.Faithful := ⟨fun {a b} φ ψ _ => (hhom a b).elim φ ψ⟩
  have : F.Full := ⟨fun {a b} φ => by
    obtain rfl : a = b := (hsub Z).elim a b
    exact ⟨𝟙 a, hpb _ _⟩⟩
  have : F.EssSurj := ⟨fun e => ⟨hZ e.fst e.snd, ⟨CategoricalPullback.mkIso
    (eqToIso ((hsub V).elim _ _)) (eqToIso ((hsub W).elim _ _)) ((hhom _ _).elim _ _)⟩⟩⟩
  exact { }

/-- Two morphisms lying over the same morphism of the base agree when `p` is faithful. -/
public theorem eq_of_isHomLift_of_faithful [p.Faithful] {R T : C} (f : R ⟶ T) {a b : 𝒳}
    (φ ψ : a ⟶ b) [p.IsHomLift f φ] [p.IsHomLift f ψ] : φ = ψ :=
  p.map_injective (by rw [IsHomLift.fac' p f φ, IsHomLift.fac' p f ψ])

/-- The identity of an object over `D.obj i` lies over `D.map (𝟙 i)`. -/
private theorem isHomLift_map_id_id {I : Type*} [Category I] (D : I ⥤ C) {i : I}
    (xi : p.Fiber (D.obj i)) : p.IsHomLift (D.map (𝟙 i)) (𝟙 xi.1) := by
  rw [D.map_id]
  exact IsHomLift.id xi.2

/-- Descent of vertical morphisms holds for a faithful functor injective on objects. -/
public theorem descentHom_of_injective [p.Faithful] (hobj : Function.Injective p.obj)
    {I : Type*} [Category I] (D : I ⥤ C) (c : Cone D) : DescentHom p D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain rfl : xi = yi := (subsingleton_fiber_of_injective p hobj _).elim _ _
  have hid := isHomLift_map_id_id p D xi
  have hφε : p.IsHomLift (c.π.app i) (φ ≫ ε) := by
    simpa using (inferInstance : p.IsHomLift (𝟙 c.pt ≫ c.π.app i) (φ ≫ ε))
  refine ⟨i, 𝟙 i, xi, xi, 𝟙 _, 𝟙 _, δ, 𝟙 _, hid, hid, hδ, IsHomLift.id xi.2,
    Category.comp_id δ, ?_⟩
  simpa using eq_of_isHomLift_of_faithful p (c.π.app i) δ (φ ≫ ε)

/-- Descent of equalities of vertical morphisms holds for a faithful functor. -/
public theorem descentEq_of_faithful_functor [p.Faithful] {I : Type*} [Category I] (D : I ⥤ C)
    (c : Cone D) : DescentEq p D c := by
  intro i xi yi x δ _ ψ ψ' hψ hψ' _
  have hid := isHomLift_map_id_id p D xi
  exact ⟨i, 𝟙 i, xi, 𝟙 _, hid, by rw [eq_of_isHomLift_of_faithful p (𝟙 (D.obj i)) ψ ψ']⟩

end ThinFibres

/-! ### Predeformation categories of a category fibred in sets -/

section FibredInSets

variable {Λ K : Type u} [CommRing Λ] [Field K] [Algebra Λ K] {S : Scheme.{u}}
  {iΛ : Spec (.of Λ) ⟶ S} {𝒴 : Type*} [Category 𝒴] {q : 𝒴 ⥤ Over S} {x₀ : 𝒴}
  {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ K)) ≫ iΛ)}

/-- The image of a faithful functor injective on objects under `Over.post` is injective on
objects. -/
public theorem over_post_obj_injective {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [F.Faithful] (hF : Function.Injective F.obj) (X : C) :
    Function.Injective (Over.post (X := X) F).obj := by
  rintro ⟨xl, ⟨⟨⟩⟩, xh⟩ ⟨yl, ⟨⟨⟩⟩, yh⟩ h
  obtain rfl : xl = yl := hF (congrArg (fun z => z.left) h)
  obtain rfl : xh = yh :=
    F.map_injective (eq_of_heq (congr_arg_heq (fun z : Over (F.obj X) => z.hom) h))
  rfl

/-- When `q` is faithful, a morphism of deformations is determined by its arrow of `𝒞_Λ`. -/
public theorem DeformationMorphism.ext_of_ringHom [q.Faithful]
    {a b : DeformationObject iΛ q x₀ hx₀} {f g : DeformationMorphism iΛ q x₀ hx₀ a b}
    (h : f.ringHom = g.ringHom) : f = g := by
  refine DeformationMorphism.ext_of_components iΛ q x₀ hx₀ h (q.map_injective ?_)
  ext1
  have hb := f.arrow_base.trans (h ▸ g.arrow_base.symm)
  rwa [cancel_epi, cancel_mono] at hb

/-- When `q` is faithful and injective on objects, a deformation is determined by its
algebra. -/
public theorem DeformationObject.eq_of_algebra_eq [q.Faithful] (hq : Function.Injective q.obj)
    {a b : DeformationObject iΛ q x₀ hx₀} (h : a.algebra = b.algebra) : a = b := by
  obtain ⟨A, y, r, hy, hr⟩ := a
  obtain ⟨A', y', r', hy', hr'⟩ := b
  dsimp only at h
  subst h
  obtain rfl : y = y' := hq (hy.trans hy'.symm)
  obtain rfl : r = r' := by
    apply q.map_injective
    ext1
    have hb := hr.trans hr'.symm
    rwa [cancel_epi, cancel_mono] at hb
  rfl

variable (P : PredeformationConstruction iΛ q x₀ hx₀)

/-- When `q` is faithful, the projection of a predeformation category to `𝒞_Λ` is faithful. -/
public theorem PredeformationConstruction.faithful_projection [q.Faithful] :
    letI := P.category
    P.projection.Faithful := by
  let := P.category
  refine ⟨fun {a b} f g hfg => (P.morphisms a b).injective
    (DeformationMorphism.ext_of_ringHom ?_)⟩
  rw [← P.morphism_projection f, ← P.morphism_projection g, hfg]

/-- When `q` is faithful and injective on objects, each fibre of a predeformation category
has at most one object. -/
public theorem PredeformationConstruction.subsingleton_fiber [q.Faithful]
    (hq : Function.Injective q.obj) (A : ArtinianLocalAlgCat.{u, u, u} Λ K) :
    letI := P.category
    Subsingleton (P.projection.Fiber A) := by
  let := P.category
  refine ⟨fun a b => Subtype.ext (P.objects.injective
    (DeformationObject.eq_of_algebra_eq hq ?_))⟩
  rw [← P.object_projection, ← P.object_projection, a.2, b.2]

end FibredInSets

/-! ### The algebra structure on global sections -/

/-- The `k[s,t]`-algebra structure on the global sections of an object of the big fppf site
over `Spec k[s,t]`, read off its structure morphism. -/
@[instance_reducible]
public def OpennessCounterexample.sectionsAlgebra
    (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) :
    Algebra (MvPolynomial (Fin 2) k) Γ((BigFppfOver.toScheme B _ hS).obj T, ⊤) :=
  (AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫
    (B.inclusion.map T.hom).appTop).hom.toAlgebra

/-- Restriction of global sections along a morphism over `Spec k[s,t]` is a map of
`k[s,t]`-algebras. -/
public theorem OpennessCounterexample.appTop_algebraMap_sectionsAlgebra
    {T T' : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} (g : T' ⟶ T)
    (r : MvPolynomial (Fin 2) k) :
    ((BigFppfOver.toScheme B _ hS).map g).appTop
        (@algebraMap _ _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T) r) =
      @algebraMap _ _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T') r := by
  have h : (B.inclusion.map T.hom).appTop ≫ ((BigFppfOver.toScheme B _ hS).map g).appTop =
      (B.inclusion.map T'.hom).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Over.w g]
    rfl
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (congrArg (AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ ·) h)) r

/-! ### Axiom [0] -/

/-- A flat local homomorphism of local rings is injective. -/
private theorem injective_of_flat_of_isLocalHom {A A' : Type*} [CommRing A] [CommRing A']
    [IsLocalRing A] [IsLocalRing A'] (f : A →+* A') (hf : f.Flat) [IsLocalHom f] :
    Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A A') := ‹IsLocalHom f›
  exact RingHom.FaithfullyFlat.injective
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr Module.FaithfullyFlat.of_flat_of_isLocalHom)

/-- Admissibility of a stalk descends along a morphism which is flat at the point. -/
public theorem isAdmissible_stalk_of_flat {T T' : Scheme.{u}} (g : T' ⟶ T)
    (τ : T ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x : T') (hg : (g.stalkMap x).hom.Flat)
    (h : @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra (g ≫ τ) x)) :
    @IsAdmissible k _ _ _ (OpennessCounterexample.stalkAlgebra τ (g x)) := by
  rw [@isAdmissible_iff_of_isLocalRing k _ _ _ _ (OpennessCounterexample.stalkAlgebra τ (g x))]
  rw [@isAdmissible_iff_of_isLocalRing k _ _ _ _
    (OpennessCounterexample.stalkAlgebra (g ≫ τ) x)] at h
  intro hs ht
  apply injective_of_flat_of_isLocalHom (g.stalkMap x).hom hg
  rw [map_zero]
  change g.stalkMap x _ = 0
  rw [OpennessCounterexample.stalkMap_algebraMap_stalkAlgebra]
  refine h ?_ ?_ <;> rw [← OpennessCounterexample.stalkMap_algebraMap_stalkAlgebra]
  exacts [map_nonunit _ _ hs, map_nonunit _ _ ht]

/-- The condition `IsArtinAxiomsObject` is local for the fppf topology: an object covered by a
covering sieve of the big fppf site whose members all satisfy it satisfies it. -/
public theorem isArtinAxiomsObject_of_mem_topology
    {U : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} {R : Sieve U}
    (hR : R ∈ BigFppfOver.topology B _ hS U)
    (h : ∀ ⦃V⦄ (f : V ⟶ U), R f → IsArtinAxiomsObject k B hS V) :
    IsArtinAxiomsObject k B hS U := by
  obtain ⟨E, hE, hle⟩ := BigFppfOver.exists_isCovering_sieve₀_le B _ hS hR
  obtain ⟨hsurj, hflat⟩ := B.jointlySurjective_and_flat_and_lfp_of_isCovering hE
  rw [isArtinAxiomsObject_iff_forall_stalk]
  intro x
  obtain ⟨i, y, rfl⟩ := hsurj x
  have hV := (isArtinAxiomsObject_iff_forall_stalk B hS (E.X i)).mp
    (h (E.f i) (hle _ (E.sieve₀_f i))) y
  rw [← toScheme_map_comp_inclusion_map_hom B hS (E.f i)] at hV
  exact isAdmissible_stalk_of_flat ((BigFppfOver.toScheme B _ hS).map (E.f i)) _ y
    (@Flat.stalkMap _ _ _ (hflat i).1 y) hV

/-- The inclusion of the full subcategory `IsArtinAxiomsObject` is fibred in sets. -/
public instance isFiberedInSets_artinAxiomsCategory :
    (ObjectProperty.ι (IsArtinAxiomsObject k B hS)).IsFiberedInSets where
  existsUnique_lift {U V} f x hx := by
    subst hx
    refine ⟨⟨⟨V, x.property.of_hom B hS f⟩, ObjectProperty.homMk f⟩, ⟨rfl, by simp⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, φ⟩ ⟨hyV, hφ⟩
    change y = V at hyV
    subst hyV
    obtain rfl : φ = ObjectProperty.homMk f := by
      ext1
      simpa using hφ
    rfl

/-- The inclusion of the full subcategory `IsArtinAxiomsObject` is a stack for the fppf
topology. -/
public theorem isStack_artinAxiomsCategory :
    (ObjectProperty.ι (IsArtinAxiomsObject k B hS)).IsStack (BigFppfOver.topology B _ hS) := by
  have hsub := subsingleton_fiber_of_injective (ObjectProperty.ι (IsArtinAxiomsObject k B hS))
    (fun a b hab => ObjectProperty.FullSubcategory.ext hab)
  refine ((Functor.isStackInSets_iff_isSheaf_objPresheaf _ _).mpr ?_).isStack
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR x _
  have hU : IsArtinAxiomsObject k B hS U := isArtinAxiomsObject_of_mem_topology B hS hR
    fun V f hf => by
      have h2 : (x f hf).1.obj = V := (x f hf).2
      exact h2 ▸ (x f hf).1.property
  exact ⟨⟨⟨U, hU⟩, rfl⟩, fun V f hf => (hsub V).elim _ _, fun t _ => (hsub U).elim _ _⟩

/-- The inclusion of the full subcategory `IsArtinAxiomsObject` is a stack in groupoids for the
fppf topology of the big fppf site over `Spec k[s,t]`. -/
@[stacks 07XR "axiom [0]: the category is a stack in groupoids, for the fppf topology"]
public theorem isStackInGroupoids_artinAxiomsCategory :
    (ObjectProperty.ι (IsArtinAxiomsObject k B hS)).IsStackInGroupoids.{w}
      (BigFppfOver.topology B _ hS) :=
  (isStack_artinAxiomsCategory B hS).isStackInGroupoids
    (isFiberedInGroupoids_artinAxiomsCategory B hS)

/-! ### Condition (RS) -/

/-- Ring maps into the global sections of an affine pushout of schemes are determined by
their composites with the two legs. -/
public theorem ringHom_ext_of_isPushout {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : X ⟶ Y}
    {i' : X' ⟶ Y'} {j' : Y ⟶ Y'} (hpo : IsPushout i j i' j') [IsAffine Y']
    {R : CommRingCat.{u}} {ψ₁ ψ₂ : R ⟶ Γ(Y', ⊤)}
    (h₁ : ψ₁ ≫ i'.appTop = ψ₂ ≫ i'.appTop) (h₂ : ψ₁ ≫ j'.appTop = ψ₂ ≫ j'.appTop) :
    ψ₁ = ψ₂ := by
  have key : ∀ (ψ : R ⟶ Γ(Y', ⊤)) {T : Scheme.{u}} (g : T ⟶ Y'),
      g ≫ Y'.toSpecΓ ≫ Spec.map ψ = T.toSpecΓ ≫ Spec.map (ψ ≫ g.appTop) := by
    intro ψ T g
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  have h : Y'.toSpecΓ ≫ Spec.map ψ₁ = Y'.toSpecΓ ≫ Spec.map ψ₂ :=
    hpo.hom_ext (by rw [key, key, h₁]) (by rw [key, key, h₂])
  exact Spec.map_inj.mp ((cancel_epi _).mp h)

/-- An object whose ring of global sections is admissible satisfies `IsArtinAxiomsObject`. -/
public theorem isArtinAxiomsObject_of_isAdmissible_sections
    (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    (h : @IsAdmissible k _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T)) :
    IsArtinAxiomsObject k B hS T :=
  (isArtinAxiomsObject_iff_forall_stalk B hS T).mpr fun x =>
    isAdmissible_of_ringHom _ _ (((BigFppfOver.toScheme B _ hS).obj T).presheaf.Γgerm x).hom
      (fun _ => rfl) h

/-- The ring of global sections of an affine object satisfying `IsArtinAxiomsObject` is
admissible. -/
public theorem isAdmissible_sections_of_isArtinAxiomsObject
    (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    [IsAffine ((BigFppfOver.toScheme B _ hS).obj T)]
    (hT : IsArtinAxiomsObject k B hS T) :
    @IsAdmissible k _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T) := by
  let Y := (BigFppfOver.toScheme B _ hS).obj T
  let τ := B.inclusion.map T.hom
  have h := isAdmissible_sections_of_stalk Γ(Y, ⊤) (Y.isoSpec.inv ≫ τ) fun x =>
    isAdmissible_stalk_of_hom Y.isoSpec.inv τ x
      ((isArtinAxiomsObject_iff_forall_stalk B hS T).mp hT _)
  refine isAdmissible_of_ringHom _ _ Y.isoSpec.hom.appTop.hom (fun r => ?_) h
  have e₀ : Y.isoSpec.inv.appTop ≫ Y.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have e : (Y.isoSpec.inv ≫ τ).appTop ≫ Y.isoSpec.hom.appTop = τ.appTop := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, e₀, Category.comp_id]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e)
    ((AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k))).hom r)

/-- In a local Artinian ring every element of the maximal ideal is nilpotent. -/
private theorem isNilpotent_of_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow ha n⟩

/-- The map `k[s,t] → k[s,t]` killing `s` and fixing `t`. -/
private def killS : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k :=
  (MvPolynomial.aeval (R := k) (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k)).toRingHom

/-- The inclusion of the full subcategory `IsArtinAxiomsObject` satisfies condition (RS): for a
pushout `Y' = Y ⨿_X X'` of finite type local Artinian schemes along a closed immersion `X → X'`,
the comparison from the fibre over `Y'` to the
two-fibre product of the fibres over `Y` and `X'` is an equivalence. -/
@[stacks 07XR "axiom [2]: the category satisfies the Rim-Schlessinger condition (RS)"]
public theorem satisfiesRS_artinAxiomsCategory :
    SatisfiesRS B _ hS (ObjectProperty.ι (IsArtinAxiomsObject k B hS))
      (isFiberedInGroupoids_artinAxiomsCategory B hS) := by
  intro T₀ T₀' T₁ T₁' i j i' j' w _ hX' hY hY' _ _ _ _ _ hpo
  let := (isFiberedInGroupoids_artinAxiomsCategory B hS).isFibered
  refine isEquivalence_fiberSquareComparison_of_injective _
    (fun a b hab => ObjectProperty.FullSubcategory.ext hab) _ _ _ _ _ _ fun a b => ?_
  obtain ⟨_, _, _⟩ := hY'
  have hYob : IsArtinAxiomsObject k B hS T₁ := a.2 ▸ a.1.property
  have hX'ob : IsArtinAxiomsObject k B hS T₀' := b.2 ▸ b.1.property
  refine ⟨⟨T₁', isArtinAxiomsObject_of_isAdmissible_sections B hS T₁' ?_⟩, rfl⟩
  rw [@isAdmissible_iff_of_isLocalRing k _ _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T₁')]
  intro hs ht
  have hvan : ∀ {D : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} (g : D ⟶ T₁'),
      IsArtinianLocal B _ hS D → IsArtinAxiomsObject k B hS D →
      ((BigFppfOver.toScheme B _ hS).map g).appTop
        (@algebraMap _ _ _ _ (OpennessCounterexample.sectionsAlgebra B hS T₁')
          (MvPolynomial.X 0)) = 0 := by
    intro D g hD hDob
    obtain ⟨_, _, _⟩ := hD
    rw [OpennessCounterexample.appTop_algebraMap_sectionsAlgebra]
    have hmem : ∀ c, c ∈ IsLocalRing.maximalIdeal Γ((BigFppfOver.toScheme B _ hS).obj T₁', ⊤) →
        ((BigFppfOver.toScheme B _ hS).map g).appTop c ∈
          IsLocalRing.maximalIdeal Γ((BigFppfOver.toScheme B _ hS).obj D, ⊤) := fun c hc =>
      (IsLocalRing.mem_maximalIdeal _).mpr
        ((isNilpotent_of_mem_maximalIdeal hc).map _).not_isUnit
    refine @eq_zero_of_isAdmissible k _ _ _ _ (OpennessCounterexample.sectionsAlgebra B hS D) ?_ ?_
      (isAdmissible_sections_of_isArtinAxiomsObject B hS D hDob) <;>
      rw [← OpennessCounterexample.appTop_algebraMap_sectionsAlgebra B hS g]
    exacts [hmem _ hs, hmem _ ht]
  let ψ : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶
      Γ((BigFppfOver.toScheme B _ hS).obj T₁', ⊤) :=
    AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ (B.inclusion.map T₁'.hom).appTop
  have hext : ∀ {D : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS} (g : D ⟶ T₁'),
      ((BigFppfOver.toScheme B _ hS).map g).appTop (ψ (MvPolynomial.X 0)) = 0 →
      ψ ≫ ((BigFppfOver.toScheme B _ hS).map g).appTop =
        (CommRingCat.ofHom killS ≫ ψ) ≫ ((BigFppfOver.toScheme B _ hS).map g).appTop := by
    intro D g hg
    ext1
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [killS]
    · intro n
      fin_cases n
      · simpa [killS] using hg
      · simp [killS]
  have h := ringHom_ext_of_isPushout hpo (hext i' (hvan i' hX' hX'ob)) (hext j' (hvan j' hY hYob))
  change ψ (X 0) = 0
  simpa [killS] using congrArg (fun φ => φ.hom (X 0)) h

/-! ### Axiom [1] -/

/-- Admissibility is witnessed by three elements: `1 = s a + t b + c` with `c s = 0`. -/
public theorem isAdmissible_iff_exists (A : Type*) [CommRing A]
    [Algebra (MvPolynomial (Fin 2) k) A] :
    IsAdmissible k A ↔ ∃ a b c : A,
      algebraMap (MvPolynomial (Fin 2) k) A (X 0) * a +
          algebraMap (MvPolynomial (Fin 2) k) A (X 1) * b + c = 1 ∧
        c * algebraMap (MvPolynomial (Fin 2) k) A (X 0) = 0 :=
  ⟨fun ⟨_, f, a, b, g, h₁, h₂⟩ => ⟨a, b, ∑ i, f i * g i, h₁, (Finset.sum_mul ..).trans
      (Finset.sum_eq_zero fun i _ => by rw [mul_right_comm, h₂ i, zero_mul])⟩,
    fun ⟨a, b, c, h₁, h₂⟩ => ⟨1, fun _ => c, a, b, fun _ => 1, by simpa using h₁, fun _ => h₂⟩⟩

/-- If the colimit of a filtered diagram of commutative rings over `k[s,t]` is admissible, then
so is some stage of the diagram. -/
public theorem exists_isAdmissible_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (φ : ∀ j, MvPolynomial (Fin 2) k →+* F.obj j)
    (hφ : ∀ {i j} (f : i ⟶ j) r, (F.map f).hom (φ i r) = φ j r)
    (ψ : MvPolynomial (Fin 2) k →+* c.pt) (hψ : ∀ j r, (c.ι.app j).hom (φ j r) = ψ r)
    (h : @IsAdmissible k _ c.pt _ ψ.toAlgebra) :
    ∃ j, @IsAdmissible k _ (F.obj j) _ (φ j).toAlgebra := by
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  have hw : ∀ {i j} (f : i ⟶ j) x, (c.ι.app j).hom ((F.map f).hom x) = (c.ι.app i).hom x :=
    fun f x => by
      rw [← c.w f]
      rfl
  have hmc : ∀ {i j l} (f : i ⟶ j) (g : j ⟶ l) x,
      (F.map (f ≫ g)).hom x = (F.map g).hom ((F.map f).hom x) := fun f g x => by
    rw [F.map_comp]
    rfl
  rw [@isAdmissible_iff_exists k _ _ _ ψ.toAlgebra] at h
  obtain ⟨a, b, e, h₁, h₂⟩ := h
  change ψ (X 0) * a + ψ (X 1) * b + e = 1 at h₁
  change e * ψ (X 0) = 0 at h₂
  obtain ⟨i₁, a', ha⟩ := Types.jointly_surjective_of_isColimit hc' a
  obtain ⟨i₂, b', hb⟩ := Types.jointly_surjective_of_isColimit hc' b
  obtain ⟨i₃, e', he⟩ := Types.jointly_surjective_of_isColimit hc' e
  change (c.ι.app i₁).hom a' = a at ha
  change (c.ι.app i₂).hom b' = b at hb
  change (c.ι.app i₃).hom e' = e at he
  let m := IsFiltered.max (IsFiltered.max i₁ i₂) i₃
  let f₁ : i₁ ⟶ m := IsFiltered.leftToMax _ _ ≫ IsFiltered.leftToMax _ _
  let f₂ : i₂ ⟶ m := IsFiltered.rightToMax _ _ ≫ IsFiltered.leftToMax _ _
  let f₃ : i₃ ⟶ m := IsFiltered.rightToMax _ _
  let A := (F.map f₁).hom a'
  let B' := (F.map f₂).hom b'
  let E := (F.map f₃).hom e'
  have hA : (c.ι.app m).hom A = a := (hw f₁ a').trans ha
  have hB : (c.ι.app m).hom B' = b := (hw f₂ b').trans hb
  have hE : (c.ι.app m).hom E = e := (hw f₃ e').trans he
  have hu : (c.ι.app m).hom (φ m (X 0) * A + φ m (X 1) * B' + E) = (c.ι.app m).hom 1 := by
    rw [map_add, map_add, map_mul, map_mul, hψ, hψ, hA, hB, hE, h₁, map_one]
  obtain ⟨k₁, g₁, hg₁⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ _).mp hu
  change (F.map g₁).hom _ = (F.map g₁).hom 1 at hg₁
  have hv : (c.ι.app k₁).hom ((F.map g₁).hom (E * φ m (X 0))) = (c.ι.app k₁).hom 0 := by
    rw [hw, map_mul, hψ, hE, h₂, map_zero]
  obtain ⟨k₂, g₂, hg₂⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ _).mp hv
  change (F.map g₂).hom _ = (F.map g₂).hom 0 at hg₂
  refine ⟨k₂, (@isAdmissible_iff_exists k _ _ _ (φ k₂).toAlgebra).mpr
    ⟨(F.map (g₁ ≫ g₂)).hom A, (F.map (g₁ ≫ g₂)).hom B', (F.map (g₁ ≫ g₂)).hom E, ?_, ?_⟩⟩
  · change φ k₂ (X 0) * _ + φ k₂ (X 1) * _ + _ = 1
    rw [← hφ (g₁ ≫ g₂) (X 0), ← hφ (g₁ ≫ g₂) (X 1), ← map_mul, ← map_mul, ← map_add,
      ← map_add, hmc, hg₁, map_one, map_one]
  · change _ * φ k₂ (X 0) = 0
    rw [← hφ (g₁ ≫ g₂) (X 0), ← map_mul, hmc, hg₂, map_zero]

/-- The full subcategory `artinAxiomsCategory`, as a category fibred in groupoids over the big
fppf site of `Spec k[s,t]`. -/
public abbrev artinAxiomsCFG :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) :=
  CatFiberedInGroupoids.mk
    { obj := artinAxiomsCategory k B hS, p := ObjectProperty.ι (IsArtinAxiomsObject k B hS) }
    (isFiberedInGroupoids_artinAxiomsCategory B hS)

/-- The category fibred in groupoids `artinAxiomsCFG` is limit preserving: for a directed
inverse system of affine schemes `Tᵢ` over `Spec k[s,t]` with limit `T`, the comparison
`colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence. -/
@[stacks 07XR "axiom [1]: the category is limit preserving, for inverse systems indexed by \
  a category in the universe of the schemes"]
public theorem isLimitPreserving_artinAxiomsCategory :
    IsLimitPreserving.{u, u, u, u + 1, u} B _ hS (artinAxiomsCFG B hS) := by
  intro I _ _ D c hc
  let p := ObjectProperty.ι (IsArtinAxiomsObject k B hS)
  have hp : p.IsFiberedInGroupoids := isFiberedInGroupoids_artinAxiomsCategory B hS
  have : p.IsFibered := hp.isFibered
  have hinj : Function.Injective p.obj := fun a b h => ObjectProperty.FullSubcategory.ext h
  refine ⟨faithful_of_descentEq p hp _ _ (descentEq_of_faithful_functor p _ _),
    full_of_descentHom p hp _ _ (descentHom_of_injective p hinj _ _),
    essSurj_of_descentObj p hp _ _ ?_⟩
  rintro ⟨⟨T, hT⟩, hTeq⟩
  change T = (BigAffineFppf.inclusion B _ hS).obj c.pt at hTeq
  subst hTeq
  have : ∀ j : Iᵒᵖ, IsAffine ((D ⋙ BigAffineFppf.toScheme B _ hS).op.obj j).unop :=
    fun j => (D.obj j.unop).property
  have hΓ := isColimitOfPreserves Scheme.Γ hc.op
  let τ := fun X : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS =>
    (AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫
      (B.inclusion.map X.hom).appTop).hom
  have : IsAffine ((BigFppfOver.toScheme B _ hS).obj
      ((BigAffineFppf.inclusion B _ hS).obj c.pt)) := c.pt.property
  obtain ⟨j, hj⟩ := exists_isAdmissible_of_isColimit (k := k) hΓ
    (fun j => τ ((BigAffineFppf.inclusion B _ hS).obj (D.obj j.unop)))
    (fun f r => OpennessCounterexample.appTop_algebraMap_sectionsAlgebra B hS
      ((BigAffineFppf.inclusion B _ hS).map (D.map f.unop)) r)
    (τ ((BigAffineFppf.inclusion B _ hS).obj c.pt))
    (fun j r => OpennessCounterexample.appTop_algebraMap_sectionsAlgebra B hS
      ((BigAffineFppf.inclusion B _ hS).map (c.π.app j.unop)) r)
    (isAdmissible_sections_of_isArtinAxiomsObject B hS _ hT)
  let xj : artinAxiomsCategory k B hS :=
    ⟨(BigAffineFppf.inclusion B _ hS).obj (D.obj j.unop),
      isArtinAxiomsObject_of_isAdmissible_sections B hS _ hj⟩
  let δ : (⟨_, hT⟩ : artinAxiomsCategory k B hS) ⟶ xj :=
    ObjectProperty.homMk ((BigAffineFppf.inclusion B _ hS).map (c.π.app j.unop))
  exact ⟨j.unop, ⟨xj, rfl⟩, δ, Functor.IsHomLift.map (p := p) δ⟩

/-! ### Axiom [3] -/

/-- The structure functor of `artinAxiomsCategory` to schemes over `Spec k[s,t]` is injective on
objects. -/
private theorem injective_artinAxiomsOver_obj :
    Function.Injective
      (ObjectProperty.ι (IsArtinAxiomsObject k B hS) ⋙ Over.post B.inclusion).obj :=
  fun _ _ h => ObjectProperty.FullSubcategory.ext
    (over_post_obj_injective B.inclusion (fun _ _ h => ObjectProperty.FullSubcategory.ext h) _ h)

/-- For every finite-type field-valued point `x₀` of `artinAxiomsCategory`, the tangent space
`T𝓕_{𝒳,k,x₀}` of its predeformation category is finite dimensional for its canonical vector space
structure, and so is the group of infinitesimal automorphisms along every split pair
`A₀ → A_ε → A₀`, for every vector space structure on it. -/
@[stacks 07XR "axiom [3]: the tangent spaces and the spaces of infinitesimal automorphisms of \
  the predeformation categories are finite dimensional"]
public theorem finiteDimensional_tangentSpace_infinitesimalAutomorphisms_artinAxiomsCategory
    {Λ K : Type u} [CommRing Λ] [Field K] [Algebra Λ K]
    (iΛ : Spec (.of Λ) ⟶ Spec (.of (MvPolynomial (Fin 2) k))) (x₀ : artinAxiomsCategory k B hS)
    (hx₀ : (ObjectProperty.ι (IsArtinAxiomsObject k B hS) ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ K)) ≫ iΛ))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ K)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ K)) ≫ iΛ)) :
    let D := predeformationCategory iΛ
      (ObjectProperty.ι (IsArtinAxiomsObject k B hS) ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    let 𝓕 := BasedCategory.ofFunctor D.projection
    let hD : Deformation.IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory B _ hS _
        (isFiberedInGroupoids_artinAxiomsCategory B hS) (satisfiesRS_artinAxiomsCategory B hS)
        iΛ x₀ hx₀ hfin hqc
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
    FiniteDimensional K
        (artinianTangentSpace Λ K (isomorphismClasses 𝓕 hD.predeformation.cofibered)) ∧
      ∀ {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ K} {z₀ : D.projection.Fiber A₀}
        {zε : D.projection.Fiber Aε} (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hge : g ≫ e = 𝟙 A₀)
        (i : z₀.1 ⟶ zε.1) (hi : D.projection.IsHomLift g i)
        [AddCommGroup ↥(infinitesimalAutomorphismsAlongSplitPair
          hD.predeformation.cofibered g e hge i hi)]
        [Module K ↥(infinitesimalAutomorphismsAlongSplitPair
          hD.predeformation.cofibered g e hge i hi)],
        FiniteDimensional K ↥(infinitesimalAutomorphismsAlongSplitPair
          hD.predeformation.cofibered g e hge i hi) := by
  intro D 𝓕 hD
  let := D.category
  have : (ObjectProperty.ι (IsArtinAxiomsObject k B hS) ⋙ Over.post B.inclusion).Faithful :=
    Functor.Faithful.comp _ _
  have hfib := D.subsingleton_fiber (injective_artinAxiomsOver_obj B hS)
  have := D.faithful_projection
  have hcl : ∀ A, Subsingleton ((isomorphismClasses 𝓕 hD.predeformation.cofibered).obj A) := by
    intro A
    have : Subsingleton (Functor.Fiber 𝓕.p A) := hfib A
    exact (Equiv.cast (isomorphismClasses_obj 𝓕 hD.predeformation.cofibered A)).subsingleton
  refine ⟨?_, fun {A₀ Aε z₀ zε} g e hge i hi _ _ => ?_⟩
  · have : Subsingleton
        (artinianTangentSpace Λ K (isomorphismClasses 𝓕 hD.predeformation.cofibered)) :=
      hcl _
    infer_instance
  · have : Subsingleton (Aut zε) := ⟨fun a b => Iso.ext
      ((subsingleton_fiber_hom_of_faithful D.projection zε zε).elim _ _)⟩
    have : Subsingleton ↥(infinitesimalAutomorphismsAlongSplitPair
        hD.predeformation.cofibered g e hge i hi) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance

end

end Deformation.Artin
