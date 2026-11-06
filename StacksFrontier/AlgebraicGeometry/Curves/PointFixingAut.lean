module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# Automorphisms of a curve which fix every point

Let `X` be a normal proper curve over a finite field `k`. The automorphisms of `X` over `k` which
fix every point of the underlying topological space form a **finite** group.

This is the input the finite-field half of [Stacks, Tag 0G05] needs and which the source leaves
as "a curve over a finite field has a finite automorphism group (details omitted)". The argument
is the one through global sections: an automorphism fixing every point preserves every local ring
inside the function field, and the local rings of a normal curve are principal ideal rings, so
the automorphism multiplies every rational function by a unit of each local ring; the resulting
quotient lies in every stalk and is therefore a global section. On a proper scheme over a finite
field there are only finitely many global sections, so each rational function has only finitely
many images, and the function field is finitely generated, so the group is finite.

## Main results

* `AlgebraicGeometry.exists_globalSection_of_mem_stalks`: an element of the function field of an
  integral scheme which lies in every stalk is a global section.
* `AlgebraicGeometry.isPrincipalIdealRing_stalk_of_normal_curve`: the local rings of a normal
  scheme of dimension at most one are principal ideal rings.
* `AlgebraicGeometry.pointFixingStalkEquiv`: the automorphism of the local ring at a fixed point
  induced by an automorphism of the scheme fixing every point.
* `AlgebraicGeometry.exists_globalSection_mul_eq_stalkEquiv`: on a normal curve such an
  automorphism acts on the function field by multiplication by a global section.
* `AlgebraicGeometry.pointFixingAutSubgroup`: the subgroup of automorphisms over the base fixing
  every point.
* `AlgebraicGeometry.finite_pointFixingAutSubgroup_of_normal_curve`: **the finiteness**.

## Implementation notes

The local ring at the generic point of an integral scheme is the function field, and the local
ring at any other point embeds in it; "lies in every stalk" is therefore phrased as a condition on
an element of `AlgebraicGeometry.Scheme.functionField`, through the algebra maps
`X.presheaf.stalk x → X.functionField`.

Dimension at most one is `topologicalKrullDim X ≤ 1`, and it enters only through the local rings:
with normality it makes each of them a field or a discrete valuation ring, which is the form
`AlgebraicGeometry.isPrincipalIdealRing_stalk_of_normal_curve` records.

A morphism fixing every point is not assumed to be the identity, and need not be: over a finite
field the Frobenius of the residue field at a closed point is an example on a zero-dimensional
scheme.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Automorphisms of a principal ideal ring -/

/-- A ring automorphism of a discrete valuation ring carries every element to an associate: it
carries a uniformiser to an irreducible element, and all irreducible elements of a discrete
valuation ring are associates. -/
theorem associated_ringEquiv_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (e : R ≃+* R) (a : R) : Associated (e a) a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
  have hπ' : Associated (e π) π :=
    IsDiscreteValuationRing.associated_of_irreducible R (hπ.map e.toMulEquiv) hπ
  have hn' : Associated (e (π ^ n)) (π ^ n) := by simpa using hπ'.pow_pow (n := n)
  exact (hn.map e.toMonoidHom).trans (hn'.trans hn.symm)

/-- A ring automorphism of a local principal ideal domain carries every element to an associate:
such a ring is a field, where every nonzero element is a unit, or a discrete valuation ring. -/
theorem associated_ringEquiv_of_isPrincipalIdealRing {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] (e : R ≃+* R) (a : R) : Associated (e a) a := by
  by_cases hR : IsField R
  · let := hR.toField
    by_cases ha : a = 0
    · simp [ha]
    have hea : e a ≠ 0 := by simpa using e.injective.ne ha
    exact (associated_one_iff_isUnit.mpr (isUnit_iff_ne_zero.mpr hea)).trans
      (associated_one_iff_isUnit.mpr (isUnit_iff_ne_zero.mpr ha)).symm
  · let : IsDiscreteValuationRing R :=
      ⟨fun hm ↦ hR (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)⟩
    exact associated_ringEquiv_of_isDiscreteValuationRing e a

/-- An automorphism of the fraction field of a local principal ideal domain which preserves the
ring multiplies every element by a unit of the ring. -/
theorem exists_unit_mul_of_fractionRing_equiv {R K : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (e : R ≃+* R) (f : K ≃+* K) (h : ∀ a, f (algebraMap R K a) = algebraMap R K (e a)) (a : K) :
    ∃ v : Rˣ, f a = algebraMap R K v * a := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) a
  obtain ⟨v, hv⟩ := associated_ringEquiv_of_isPrincipalIdealRing e b
  obtain ⟨w, hw⟩ := associated_ringEquiv_of_isPrincipalIdealRing e (s : R)
  refine ⟨w * v⁻¹, ?_⟩
  dsimp only
  rw [IsFractionRing.mk'_eq_div, map_div₀, h, h]
  have hb : e b = b * (v⁻¹ : Rˣ) := (Units.eq_mul_inv_iff_mul_eq (c := _)).mpr hv
  have hs : e (s : R) = (s : R) * (w⁻¹ : Rˣ) := (Units.eq_mul_inv_iff_mul_eq (c := _)).mpr hw
  rw [hb, hs]
  simp only [map_mul, Units.val_mul, map_units_inv]
  have hw0 : algebraMap R K (w : R) ≠ 0 := (w.isUnit.map (algebraMap R K)).ne_zero
  field_simp [hw0]

/-! ### Algebraic Hartogs through the stalks -/

/-- **An element of the function field of an integral scheme which lies in every stalk is a
global section.** The local representatives agree on overlaps because the germ map at the generic
point of an integral scheme is injective, so they glue. -/
theorem exists_globalSection_of_mem_stalks (X : Scheme.{u}) [IsIntegral X]
    [Nonempty (⊤ : X.Opens)] (a : X.functionField)
    (ha : ∀ x : X, ∃ b : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField b = a) :
    ∃ b : Γ(X, ⊤), X.germToFunctionField ⊤ b = a := by
  classical
  have hlocal (x : X) : ∃ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      ∃ hU : Nonempty U, @Scheme.germToFunctionField X _ U hU b = a := by
    obtain ⟨b, hb⟩ := ha x
    obtain ⟨U, hx, c, hc⟩ := X.presheaf.exists_germ_eq b
    let : Nonempty U := ⟨⟨x, hx⟩⟩
    exact ⟨U, hx, c, inferInstance, by
      rw [← X.algebraMap_germ_eq_germToFunctionField hx c, hc, hb]⟩
  choose U hx b hU hb using hlocal
  let (x : X) : Nonempty (U x) := hU x
  have hgen (x : X) : genericPoint X ∈ U x :=
    ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr ⟨x, trivial, hx x⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U b := by
    intro i j
    have hmem : genericPoint X ∈ U i ⊓ U j := ⟨hgen i, hgen j⟩
    apply germ_injective_of_isIntegral X (U := U i ⊓ U j) (genericPoint X) hmem
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hb i).trans (hb j).symm
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun i ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) b hcompat
  refine ⟨c, ?_⟩
  rw [← hb (genericPoint X), ← hc (genericPoint X)]
  exact (X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
    (hgen (genericPoint X)) c).symm

/-- **The local rings of a normal scheme of dimension at most one are principal ideal rings.**
They are Noetherian local domains, integrally closed because the scheme is normal, and of Krull
dimension at most one, which is one of the equivalent characterisations of a discrete valuation
ring or a field. -/
theorem isPrincipalIdealRing_stalk_of_normal_curve (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : topologicalKrullDim X ≤ 1) (x : X) :
    IsPrincipalIdealRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    refine (Order.coheight_le_krullDim x).trans ?_
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr hdim
  have ht : IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ∀ I : Ideal (X.presheaf.stalk x), I ≠ ⊥ → I.IsPrime →
        I = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    ⟨IsNormal.stalk_normal x, fun I hI hIp ↦
      IsLocalRing.eq_maximalIdeal (hIp.isMaximal_of_ne_bot hI)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 4 1).mp ht

/-! ### The local automorphisms induced by an automorphism fixing every point -/

/-- The automorphism of the local ring at a point induced by an automorphism of a scheme which
fixes every point of the underlying topological space. -/
noncomputable def pointFixingStalkEquiv {X : Scheme.{u}} (f : X ⟶ X) [IsIso f]
    (h : ∀ x, f x = x) (x : X) : X.presheaf.stalk x ≃+* X.presheaf.stalk x :=
  (asIso (eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) (h x).symm) ≫
    f.stalkMap x)).commRingCatIsoToRingEquiv

/-- Comparison of the transport isomorphisms of two equal pairs of specializing points. -/
private lemma stalkSpecializes_congr {X : Scheme.{u}} {x x' y y' : X} (hx : x' = x) (hy : y' = y)
    (hs : y ⤳ x) (hs' : y' ⤳ x') :
    eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) hx.symm) ≫ X.presheaf.stalkSpecializes hs' =
      X.presheaf.stalkSpecializes hs ≫ eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) hy.symm) := by
  subst hx hy
  simp

/-- The local automorphisms of `AlgebraicGeometry.pointFixingStalkEquiv` are compatible with the
inclusions of the local rings into the function field. -/
theorem pointFixingStalkEquiv_algebraMap {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) [IsIso f]
    (h : ∀ x, f x = x) (x : X) (a : X.presheaf.stalk x) :
    pointFixingStalkEquiv f h (genericPoint X)
        (algebraMap (X.presheaf.stalk x) X.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (pointFixingStalkEquiv f h x a) := by
  have hn := f.stalkSpecializes_stalkMap (genericPoint X) x (genericPoint_specializes x)
  have hc := stalkSpecializes_congr (h x) (h (genericPoint X)) (genericPoint_specializes x)
    (f.base.hom.map_specializes (genericPoint_specializes x))
  have hh := congrArg
    (fun g ↦ eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) (h x).symm) ≫ g) hn
  rw [← Category.assoc, hc, Category.assoc] at hh
  exact congrArg (fun g : X.presheaf.stalk x ⟶ X.functionField ↦ g a) hh

/-- **On a normal curve, an automorphism fixing every point multiplies every rational function by
a global section.** At each point the automorphism preserves the local ring, which is a principal
ideal ring, so it multiplies the function by a unit there; the quotient lies in every stalk and is
therefore a global section. -/
theorem exists_globalSection_mul_eq_stalkEquiv (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [Nonempty (⊤ : X.Opens)]
    (hX : topologicalKrullDim X ≤ 1) (f : X ⟶ X) [IsIso f] (h : ∀ x, f x = x)
    (a : X.functionField) :
    ∃ b : Γ(X, ⊤), X.germToFunctionField ⊤ b * a =
      pointFixingStalkEquiv f h (genericPoint X) a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  let g := pointFixingStalkEquiv f h (genericPoint X)
  have hlocal (x : X) : ∃ b : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField b = g a / a := by
    let := isPrincipalIdealRing_stalk_of_normal_curve X hX x
    obtain ⟨v, hv⟩ := exists_unit_mul_of_fractionRing_equiv (pointFixingStalkEquiv f h x) g
      (pointFixingStalkEquiv_algebraMap f h x) a
    exact ⟨v, (eq_div_iff ha).mpr hv.symm⟩
  obtain ⟨b, hb⟩ := exists_globalSection_of_mem_stalks X (g a / a) hlocal
  exact ⟨b, by rw [hb, div_mul_cancel₀ _ ha]⟩

/-! ### The group of automorphisms fixing every point -/

/-- The subgroup of the automorphisms of a scheme over a base consisting of those which fix every
point of the underlying topological space. -/
def pointFixingAutSubgroup {X S : Scheme.{u}} (p : X ⟶ S) : Subgroup (Aut (Over.mk p)) where
  carrier := {a | ∀ x, a.asIso.hom.left x = x}
  one_mem' _ := rfl
  mul_mem' := by
    intro a b ha hb x
    change a.asIso.hom.left (b.asIso.hom.left x) = x
    rw [hb, ha]
  inv_mem' := by
    intro a ha x
    have hi : a.asIso.hom.left (a.asIso.inv.left x) = x := by
      change (a.asIso.inv.left ≫ a.asIso.hom.left) x = x
      rw [← Over.comp_left, a.asIso.inv_hom_id]
      rfl
    exact (ha _).symm.trans hi

/-- The automorphism of the function field induced by a point-fixing automorphism. -/
noncomputable def pointFixingAutFunctionField {X : Scheme.{u}} [IsIntegral X] {S : Scheme.{u}}
    (p : X ⟶ S) (a : pointFixingAutSubgroup p) : X.functionField ≃+* X.functionField :=
  letI : IsIso a.val.asIso.hom := ⟨a.val.asIso.inv, a.val.asIso.hom_inv_id, a.val.asIso.inv_hom_id⟩
  letI : IsIso a.val.asIso.hom.left := (Over.forget S).map_isIso a.val.asIso.hom
  pointFixingStalkEquiv a.val.asIso.hom.left a.property (genericPoint X)

/-- Transporting the canonical morphism from the spectrum of a local ring along an equality of
points. -/
private lemma fromSpecStalk_congr {X : Scheme.{u}} {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

/-- The transport of `AlgebraicGeometry.pointFixingStalkEquiv` along the canonical morphism from
the spectrum of the local ring. -/
private lemma pointFixingStalkEquiv_fromSpecStalk {X : Scheme.{u}} (f : X ⟶ X) [IsIso f]
    (h : ∀ x, f x = x) (x : X) :
    Spec.map (CommRingCat.ofHom (pointFixingStalkEquiv f h x).toRingHom) ≫
      X.fromSpecStalk x = X.fromSpecStalk x ≫ f := by
  have hco : CommRingCat.ofHom (pointFixingStalkEquiv f h x).toRingHom =
      eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) (h x).symm) ≫ f.stalkMap x := rfl
  rw [hco, Spec.map_comp, Category.assoc, fromSpecStalk_congr (h x).symm,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The underlying morphism of schemes of an automorphism over the base is an isomorphism. -/
private lemma isIso_hom_left {X S : Scheme.{u}} {p : X ⟶ S} (a : Aut (Over.mk p)) :
    IsIso a.asIso.hom.left :=
  haveI : IsIso a.asIso.hom := ⟨a.asIso.inv, a.asIso.hom_inv_id, a.asIso.inv_hom_id⟩
  (Over.forget S).map_isIso a.asIso.hom

/-- A point-fixing automorphism of an integral scheme separated over the base is determined by
the automorphism it induces on the function field. -/
theorem pointFixingAutFunctionField_injective {X : Scheme.{u}} [IsIntegral X] {S : Scheme.{u}}
    (p : X ⟶ S) [IsSeparated p] : Function.Injective (pointFixingAutFunctionField p) := by
  intro a b hab
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  apply Over.OverMorphism.ext
  let : IsDominant (X.fromSpecStalk (genericPoint X)) := isDominant_fromSpecStalk_genericPoint X
  apply ext_of_isDominant_of_isSeparated p ((Over.w _).trans (Over.w _).symm)
    (X.fromSpecStalk (genericPoint X))
  have := isIso_hom_left a.val
  have := isIso_hom_left b.val
  exact (pointFixingStalkEquiv_fromSpecStalk (X := X) a.val.asIso.hom.left a.property
    (genericPoint X)).symm.trans ((congrArg (fun e : X.functionField ≃+* X.functionField ↦
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X)) hab).trans
        (pointFixingStalkEquiv_fromSpecStalk (X := X) b.val.asIso.hom.left b.property
          (genericPoint X)))

/-- A group of automorphisms of the fraction field of an algebra of finite type over a finite
ring, acting with finite orbits, is finite: an automorphism is determined by its values on the
finitely many algebra generators and on the base ring. -/
theorem finite_of_finite_range_ringEquiv (k A K : Type*) [CommRing k] [CommRing A] [Field K]
    [Algebra k A] [Algebra.FiniteType k A] [Finite k] [Algebra A K] [IsFractionRing A K]
    {G : Type*} (e : G → K ≃+* K) (he : Function.Injective e)
    (hfinite : ∀ x : K, (Set.range (fun g ↦ e g x)).Finite) : Finite G := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let v : k ⊕ s → K := Sum.elim
    (fun x ↦ algebraMap A K (algebraMap k A x)) (fun x ↦ algebraMap A K (x : A))
  let (i : k ⊕ s) : Finite (Set.range (fun g ↦ e g (v i))) := (hfinite (v i)).to_subtype
  let ev (g : G) : ∀ i : k ⊕ s, Set.range (fun g ↦ e g (v i)) := fun i ↦ ⟨e g (v i), g, rfl⟩
  apply Finite.of_injective ev
  intro a b hab
  apply he
  have hval (i : k ⊕ s) : e a (v i) = e b (v i) := congrArg Subtype.val (congrFun hab i)
  have heq (z : A) : e a (algebraMap A K z) = e b (algebraMap A K z) := by
    have hz : z ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem z hz => exact hval (.inr ⟨z, hz⟩)
    | algebraMap r => exact hval (.inl r)
    | add x y hx hy hfx hfy => simp only [map_add, hfx, hfy]
    | mul x y hx hy hfx hfy => simp only [map_mul, hfx, hfy]
  have hh : (e a).toRingHom = (e b).toRingHom := IsFractionRing.ringHom_ext (A := A) heq
  exact RingEquiv.ext fun x ↦ DFunLike.congr_fun hh x

/-- The ring of global sections of an integral scheme proper over a finite field is finite: it is
a finite module over the finite ring of global sections of the base. -/
theorem finite_globalSections_of_finite_field (k : Type u) [Field k] [Finite k] (X : Scheme.{u})
    [IsIntegral X] (p : X ⟶ Spec (.of k)) [UniversallyClosed p] [LocallyOfFiniteType p] :
    Finite Γ(X, ⊤) := by
  let : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_equiv k (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toEquiv
  let : Algebra Γ(Spec (.of k), ⊤) Γ(X, ⊤) := p.appTop.hom.toAlgebra
  let : Module.Finite Γ(Spec (.of k), ⊤) Γ(X, ⊤) := finite_appTop_of_universallyClosed k p
  exact Module.finite_of_finite (R := Γ(Spec (.of k), ⊤))

/-- **The automorphisms of a normal proper curve over a finite field which fix every point of the
underlying topological space form a finite group.**

This is the input of the finite-field half of [Stacks, Tag 0G05] that the source states as "a
curve over a finite field has a finite automorphism group (details omitted)", in the form the
argument needs. Such an automorphism multiplies every rational function by a global section
(`AlgebraicGeometry.exists_globalSection_mul_eq_stalkEquiv`), the global sections are finite in
number because the curve is proper over a finite field, the function field is the fraction field
of an algebra of finite type over `k`, and an automorphism of the function field determines the
automorphism of the curve. -/
theorem finite_pointFixingAutSubgroup_of_normal_curve (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hX : topologicalKrullDim X ≤ 1) : Finite (pointFixingAutSubgroup p) := by
  classical
  let : LocallyOfFiniteType p := IsProper.toLocallyOfFiniteType
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Finite Γ(X, ⊤) := finite_globalSections_of_finite_field k X p
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  let : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  let scalars : k →+* Γ(X, U) :=
    (p.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, U) := scalars.toAlgebra
  have hf : (p.appLE ⊤ U (by simp)).hom.FiniteType :=
    p.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  let : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (hf.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective))
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply finite_of_finite_range_ringEquiv k Γ(X, U) X.functionField (pointFixingAutFunctionField p)
    (pointFixingAutFunctionField_injective p)
  intro x
  apply (Set.finite_range (fun c : Γ(X, ⊤) ↦ X.germToFunctionField ⊤ c * x)).subset
  rintro _ ⟨a, rfl⟩
  have := isIso_hom_left a.val
  exact exists_globalSection_mul_eq_stalkEquiv X hX a.val.asIso.hom.left a.property x

end AlgebraicGeometry

end
