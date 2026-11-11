module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.DiagonalKernel

/-!
# The diagonal of a coproduct in the big crystalline category `CRIS(C/A)`

Fix an affine crystalline situation with base `(A, I, γ)` and target `C`, and let `X = (B, J, δ)`
be an arbitrary divided power thickening of `C` over `A`, that is, an object of the big
crystalline category `CRIS(C/A)` (the structural map `C → B/J` need not be an isomorphism).  Let
`Y = (B(1), J(1), δ(1))` be a coproduct of `X` with itself in `CRIS(C/A)`, with coprojections
`s₀, s₁ : X → Y`, and let `Y → X` be the codiagonal.  Write `K` for the kernel of the codiagonal
on underlying rings.

Here `K` need not be contained in `J(1)`, and the intersection `K ∩ J(1)` is stable under the
divided powers of `Y`, being the intersection of a kernel of a divided power map with the divided
power ideal.  The quotient `K / (K² + (K ∩ J(1))^{[2]})` is the diagonal conormal module.

## Main definitions

* `Crystalline.DividedPowerThickening.firstOrderExtensionThickening` — the first-order thickening
  `B ⊕ M` of an object of `CRIS(C/A)` by a module, again an object of `CRIS(C/A)`.
* `Crystalline.DividedPowerThickening.diagonalMap` — the codiagonal `B(1) → B`.
* `Crystalline.DividedPowerThickening.diagonalKernel` — its kernel `K`.
* `Crystalline.DividedPowerThickening.diagonalRelations` — `K² + (K ∩ J(1))^{[2]}` inside `K`.
* `Crystalline.DividedPowerThickening.diagonalConormal` — the quotient of `K` by the relations.
* `Crystalline.DividedPowerThickening.diagonalDifference` — the class of `s₁ b - s₀ b`.

## Main results

* `Crystalline.DividedPowerThickening.diagonalKernel_isSubDPIdeal` — Stacks 07HV, part (1).

The canonical identification of part (2) is
`Crystalline.DividedPowerThickening.dividedPowerDifferentialsEquivDiagonalConormal`, in
`StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.CRISConormalEquiv`.

## Implementation notes

These declarations generalize those of the same names in the namespace `Crystalline`, which are
stated for the full subcategory `Cris(C/A)` and its coproducts, to arbitrary objects of
`CRIS(C/A)` with a coproduct in `CRIS(C/A)`.  The coproduct is given by an `IsColimit` hypothesis
on a binary cofan in `CRIS(C/A)`.

## References

* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DividedPowerRing

universe u v w

namespace Crystalline

namespace DividedPowerThickening

/-- The first-order thickening of an object `(B, J, δ)` of `CRIS(C/A)` by a `B`-module `M`: the
trivial square-zero extension `B ⊕ M` with ideal `J ⊕ M`, its divided powers, and the structural
map `C → B/J = (B ⊕ M)/(J ⊕ M)`. -/
noncomputable abbrev firstOrderExtensionThickening
    {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M] : DividedPowerThickening S := by
  classical
  let D := X.ring
  let T := firstOrderExtension D M
  let J := firstOrderExtensionIdeal D M
  let hdp := firstOrderExtension_dividedPowers D M
  let δ := Classical.choose hdp
  have hmor := (Classical.choose_spec hdp).2
  let C : DividedPowerRing := ⟨T, J, δ⟩
  let base : DividedPowers.DPMorphism S.A.dividedPowers C.dividedPowers :=
    (DividedPowers.DPMorphism.mk' hmor).comp X.fromBase
  have hinl : D.ideal ≤ Ideal.comap (TrivSqZeroExt.inlHom D M) C.ideal := by
    intro x hx
    change (TrivSqZeroExt.fstHom D D M).toRingHom
      (TrivSqZeroExt.inlHom D M x) ∈ D.ideal
    simpa using hx
  let q : (D ⧸ D.ideal) →+* (C ⧸ C.ideal) :=
    firstOrderExtensionQuotientMap D M
  refine ⟨C, base, ?_, q.comp X.toQuotient, ?_⟩
  · change IsNilpotent (TrivSqZeroExt.inl (S.p : D))
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using
      X.prime_nilpotent.map (algebraMap D T)
  · ext a
    have hxa := congrArg (fun f : S.A →+* D ⧸ D.ideal => (q.comp f) a) X.commutes
    have hi : (algebraMap D T : D →+* T) = TrivSqZeroExt.inlHom D M := by
      ext x
      · simp [T, firstOrderExtension, TrivSqZeroExt.algebraMap_eq_inl,
          TrivSqZeroExt.inlHom, TrivSqZeroExt.fst]
      · rfl
    change Ideal.Quotient.mk C.ideal
      (algebraMap D T (X.fromBase.toRingHom a)) =
      q (X.toQuotient (algebraMap S.A S.C a))
    rw [hi]
    change q (Ideal.Quotient.mk D.ideal (X.fromBase.toRingHom a)) =
      q (X.toQuotient (algebraMap S.A S.C a)) at hxa
    simp only [DividedPowers.DPMorphism.toRingHom_apply] at hxa
    exact hxa

/-- The inclusion `b ↦ (b, 0)` of an object of `CRIS(C/A)` into its first-order thickening. -/
noncomputable def firstOrderExtensionMapZero
    {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M] :
    X ⟶ firstOrderExtensionThickening X M := by
  classical
  let D := X.ring
  let hdp := firstOrderExtension_dividedPowers D M
  let δ := Classical.choose hdp
  have hmor := (Classical.choose_spec hdp).2
  let f : DividedPowers.DPMorphism D.dividedPowers δ :=
    DividedPowers.DPMorphism.mk' hmor
  let E := firstOrderExtensionThickening X M
  refine { hom := f, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · rfl
  · change (Ideal.quotientMap E.ring.ideal f.toRingHom
      (Ideal.map_le_iff_le_comap.mp f.ideal_comp)).comp X.toQuotient =
      E.toQuotient
    rfl

/-- The graph `b ↦ (b, θ b)` of a divided power derivation `θ`, as a morphism of `CRIS(C/A)`
into the first-order thickening. -/
noncomputable def firstOrderExtensionMapGraph
    {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    X ⟶ firstOrderExtensionThickening X M := by
  classical
  let D := X.ring
  let hdp := firstOrderExtension_dividedPowers D M
  let f := graphDPMorphism d hdp
  let E := firstOrderExtensionThickening X M
  refine { hom := f, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_ringHom a
  · change (Ideal.quotientMap E.ring.ideal f.toRingHom
      (Ideal.map_le_iff_le_comap.mp f.ideal_comp)).comp X.toQuotient =
      E.toQuotient
    change (Ideal.quotientMap (firstOrderExtensionIdeal D M)
      (graphRingHom d) _).comp X.toQuotient =
      (firstOrderExtensionQuotientMap D M).comp X.toQuotient
    rw [graphQuotientMap_eq_inl d]

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : DividedPowerThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

/-- The codiagonal `B(1) → B` out of a coproduct of an object of `CRIS(C/A)` with itself. -/
public noncomputable def diagonalMap (h : IsColimit (BinaryCofan.mk s₀ s₁)) : Y ⟶ X :=
  h.desc (BinaryCofan.mk (𝟙 X) (𝟙 X))

/-- The kernel `K = Ker(B(1) → B)` of the codiagonal. -/
public noncomputable abbrev diagonalKernel (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Ideal Y.ring :=
  RingHom.ker (diagonalMap h).hom.toRingHom

/-- The square and higher divided-power relations inside the diagonal kernel. -/
public noncomputable def diagonalRelations (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Submodule Y.ring (diagonalKernel h) :=
  Submodule.comap
    (Submodule.subtype ((diagonalKernel h : Ideal Y.ring) : Submodule Y.ring Y.ring))
    ((((diagonalKernel h) ^ (2 : ℕ)) +
      secondDividedPowerIdeal Y.ring.dividedPowers
        (diagonalKernel h ⊓ Y.ring.ideal) : Ideal Y.ring) : Submodule Y.ring Y.ring)

/-- The diagonal conormal module, with its `X.ring`-module structure induced by the
first coprojection. -/
public noncomputable def diagonalConormal (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Type w :=
  RestrictScalars X.ring Y.ring ((diagonalKernel h) ⧸ diagonalRelations h)

/-- The additive group structure on the diagonal conormal module. -/
public noncomputable instance (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    AddCommGroup (diagonalConormal h) :=
  inferInstanceAs (AddCommGroup
    (RestrictScalars X.ring Y.ring ((diagonalKernel h) ⧸ diagonalRelations h)))

/-- The `X.ring`-module structure on the diagonal conormal module, by restriction of
scalars along the first coprojection. -/
public noncomputable instance (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Module X.ring (diagonalConormal h) := by
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  exact inferInstanceAs (Module X.ring
    (RestrictScalars X.ring Y.ring ((diagonalKernel h) ⧸ diagonalRelations h)))

/-- The class of the difference of the two coprojections in the diagonal conormal module. -/
public noncomputable def diagonalDifference (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (b : X.ring) : diagonalConormal h :=
  Submodule.Quotient.mk ⟨s₁.hom b - s₀.hom b, by
    rw [RingHom.mem_ker]
    change (diagonalMap h).hom.toRingHom
      (s₁.hom.toRingHom b - s₀.hom.toRingHom b) = 0
    rw [map_sub]
    have h₁ : s₁ ≫ diagonalMap h = 𝟙 X := BinaryCofan.IsColimit.inr_desc h (𝟙 X) (𝟙 X)
    have h₀ : s₀ ≫ diagonalMap h = 𝟙 X := BinaryCofan.IsColimit.inl_desc h (𝟙 X) (𝟙 X)
    have hb₁ := congrArg (fun q : X ⟶ X ↦ q.hom.toRingHom b) h₁
    have hb₀ := congrArg (fun q : X ⟶ X ↦ q.hom.toRingHom b) h₀
    change (diagonalMap h).hom.toRingHom (s₁.hom.toRingHom b) = b at hb₁
    change (diagonalMap h).hom.toRingHom (s₀.hom.toRingHom b) = b at hb₀
    rw [hb₁, hb₀, sub_self]⟩

/-- The element `y - s₀(Δ y)` of the diagonal kernel, where `Δ` is the codiagonal. -/
noncomputable def diagonalClassRep
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (y : Y.ring) : diagonalKernel h :=
  ⟨y - s₀.hom ((diagonalMap h).hom y), by
    rw [RingHom.mem_ker]
    change (diagonalMap h).hom.toRingHom
      (y - s₀.hom.toRingHom ((diagonalMap h).hom y)) = 0
    rw [map_sub]
    have hs₀ : (diagonalMap h).hom.toRingHom
        (s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y)) =
        (diagonalMap h).hom.toRingHom y := by
      have hc : s₀ ≫ diagonalMap h = 𝟙 X :=
        BinaryCofan.IsColimit.inl_desc h (𝟙 X) (𝟙 X)
      have hb := congrArg (fun q : X ⟶ X => q.hom.toRingHom
        ((diagonalMap h).hom.toRingHom y)) hc
      change (diagonalMap h).hom.toRingHom
        (s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y)) = _ at hb
      exact hb
    change (diagonalMap h).hom.toRingHom y -
      (diagonalMap h).hom.toRingHom
        (s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y)) = 0
    rw [hs₀, sub_self]⟩

/-- The class of `y - s₀(Δ y)` in the diagonal conormal module. -/
noncomputable def diagonalClass
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (y : Y.ring) : diagonalConormal h :=
  Submodule.Quotient.mk (diagonalClassRep h y)

/-- The class map is additive. -/
theorem diagonalClass_add
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (y z : Y.ring) :
    diagonalClass h (y + z) = diagonalClass h y + diagonalClass h z := by
  dsimp only [diagonalClass]
  change Submodule.Quotient.mk (diagonalClassRep h (y + z)) =
    Submodule.Quotient.mk (diagonalClassRep h y + diagonalClassRep h z)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  dsimp only [diagonalClassRep]
  change y + z - s₀.hom.toRingHom
      ((diagonalMap h).hom.toRingHom (y + z)) =
    (y - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y)) +
      (z - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom z))
  rw [map_add ((diagonalMap h).hom.toRingHom) y z]
  rw [map_add s₀.hom.toRingHom
    ((diagonalMap h).hom.toRingHom y) ((diagonalMap h).hom.toRingHom z)]
  abel_nf

/-- The diagonal conormal module is additively the quotient of the kernel by the relations. -/
noncomputable def diagonalConormalAddEquiv
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalConormal h ≃+ (diagonalKernel h) ⧸ diagonalRelations h :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := by intros; rfl }

/-- The diagonal conormal module is the quotient of the kernel by the relations, with scalars
restricted along the first coprojection. -/
noncomputable def diagonalConormalLinearEquiv
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
    diagonalConormal h ≃ₗ[X.ring]
      (diagonalKernel h) ⧸ diagonalRelations h := by
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  letI : Module X.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.toRingHom
  refine { toAddEquiv := diagonalConormalAddEquiv h, map_smul' := ?_ }
  intro a x
  rfl

/-- The identification `diagonalConormalLinearEquiv` is the identity on elements. -/
theorem diagonalConormalLinearEquiv_apply
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (x : diagonalConormal h) : diagonalConormalLinearEquiv h x = x := rfl

/-- A class in the diagonal conormal module is a combination of two others, with coefficients in
`X.ring`, as soon as the difference of representatives lies in the relations. -/
private theorem diagonalClass_eq_smul_add_smul
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) (w z z' : Y.ring) (a b : X.ring)
    (hmem : (diagonalClassRep h w : Y.ring) -
      (s₀.hom a * diagonalClassRep h z + s₀.hom b * diagonalClassRep h z') ∈
      diagonalKernel h ^ (2 : ℕ) + secondDividedPowerIdeal Y.ring.dividedPowers
        (diagonalKernel h ⊓ Y.ring.ideal)) :
    diagonalClass h w = a • diagonalClass h z + b • diagonalClass h z' := by
  let : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let : Module X.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.toRingHom
  apply (diagonalConormalLinearEquiv h).injective
  rw [(diagonalConormalLinearEquiv h).map_add, (diagonalConormalLinearEquiv h).map_smul,
    (diagonalConormalLinearEquiv h).map_smul, diagonalConormalLinearEquiv_apply,
    diagonalConormalLinearEquiv_apply, diagonalConormalLinearEquiv_apply]
  change Submodule.Quotient.mk (diagonalClassRep h w) =
    s₀.hom.toRingHom a • (Submodule.Quotient.mk (diagonalClassRep h z) :
          (diagonalKernel h) ⧸ diagonalRelations h) +
      s₀.hom.toRingHom b • (Submodule.Quotient.mk (diagonalClassRep h z') :
          (diagonalKernel h) ⧸ diagonalRelations h)
  rw [← Submodule.Quotient.mk_smul (R := Y.ring)
      (M := diagonalKernel h) (p := diagonalRelations h) (S := Y.ring),
    ← Submodule.Quotient.mk_smul (R := Y.ring)
      (M := diagonalKernel h) (p := diagonalRelations h) (S := Y.ring),
    ← Submodule.Quotient.mk_add]
  exact (Submodule.Quotient.eq (diagonalRelations h)).2 hmem

/-- The class map satisfies the Leibniz rule over the codiagonal. -/
theorem diagonalClass_mul
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (y z : Y.ring) :
    diagonalClass h (y * z) =
      (diagonalMap h).hom y • diagonalClass h z +
        (diagonalMap h).hom z • diagonalClass h y := by
  refine diagonalClass_eq_smul_add_smul h _ _ _ _ _ ?_
  have heq : (diagonalClassRep h (y * z) : Y.ring) -
      (s₀.hom ((diagonalMap h).hom y) * diagonalClassRep h z +
        s₀.hom ((diagonalMap h).hom z) * diagonalClassRep h y) =
      (diagonalClassRep h y : Y.ring) * (diagonalClassRep h z : Y.ring) := by
    change (y * z - s₀.hom.toRingHom
        ((diagonalMap h).hom.toRingHom (y * z))) -
      (s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y) *
          (z - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom z)) +
        s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom z) *
          (y - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y))) =
      (y - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom y)) *
        (z - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom z))
    rw [map_mul ((diagonalMap h).hom.toRingHom) y z, map_mul s₀.hom.toRingHom]
    ring
  rw [heq, pow_two]
  exact Submodule.mem_sup_left (Ideal.mul_mem_mul (diagonalClassRep h y).property
    (diagonalClassRep h z).property)

/-- The class of `δ_n(y)` is `δ_{n-1}(Δ y)` times the class of `y`, for `y ∈ J(1)`, `n ≥ 2`. -/
theorem diagonalClass_dpow
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (n : ℕ) (y : Y.ring) (hn : 2 ≤ n) (hy : y ∈ Y.ring.ideal) :
    diagonalClass h (Y.ring.dividedPowers.dpow n y) =
      X.ring.dividedPowers.dpow (n - 1) ((diagonalMap h).hom y) •
        diagonalClass h y := by
  refine (diagonalClass_eq_smul_add_smul h _ y y
    (X.ring.dividedPowers.dpow (n - 1) ((diagonalMap h).hom y)) 0 ?_).trans
    (by rw [zero_smul, add_zero])
  rw [show s₀.hom 0 = 0 from map_zero s₀.hom.toRingHom, zero_mul, add_zero]
  let q := (diagonalMap h).hom.toRingHom
  let a := s₀.hom.toRingHom (q y)
  let k := diagonalClassRep h y
  let I₂ := secondDividedPowerIdeal Y.ring.dividedPowers
    (diagonalKernel h ⊓ Y.ring.ideal)
  have hqy : q y ∈ X.ring.ideal :=
    (Ideal.map_le_iff_le_comap.mp (diagonalMap h).hom.ideal_comp) hy
  have ha : a ∈ Y.ring.ideal :=
    (Ideal.map_le_iff_le_comap.mp s₀.hom.ideal_comp) hqy
  have hkK : (k : Y.ring) ∈ diagonalKernel h := k.property
  have hkI : (k : Y.ring) ∈ Y.ring.ideal := by
    dsimp [k, diagonalClassRep]
    exact sub_mem hy ha
  have hyak : y = a + (k : Y.ring) := by
    change y = s₀.hom.toRingHom (q y) +
      (y - s₀.hom.toRingHom (q y))
    abel
  let F (i : ℕ) := Y.ring.dividedPowers.dpow i a *
    Y.ring.dividedPowers.dpow (n - i) (k : Y.ring)
  have hadd : Y.ring.dividedPowers.dpow n y =
      ∑ i ∈ Finset.range (n + 1), F i := by
    rw [hyak]
    exact Y.ring.dividedPowers.dpow_add' ha hkI
  have hsplit : (∑ i ∈ Finset.range (n + 1), F i) =
      (∑ i ∈ Finset.range (n - 1), F i) + F (n - 1) + F n := by
    rw [show n + 1 = (n - 1 + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [show n - 1 + 1 = n by omega]
  have hFn : F n = Y.ring.dividedPowers.dpow n a := by
    dsimp [F]
    rw [Nat.sub_self, Y.ring.dividedPowers.dpow_zero hkI, mul_one]
  have hFnm1 : F (n - 1) =
      Y.ring.dividedPowers.dpow (n - 1) a * (k : Y.ring) := by
    dsimp [F]
    rw [show n - (n - 1) = 1 by omega,
      Y.ring.dividedPowers.dpow_one hkI]
  have hcalc : Y.ring.dividedPowers.dpow n y -
      Y.ring.dividedPowers.dpow n a -
        Y.ring.dividedPowers.dpow (n - 1) a * (k : Y.ring) =
      ∑ i ∈ Finset.range (n - 1), F i := by
    rw [hadd, hsplit, hFnm1, hFn]
    ring
  have htail : (∑ i ∈ Finset.range (n - 1), F i) ∈ I₂ := by
    apply Submodule.sum_mem
    intro i hi
    have hi' : i < n - 1 := Finset.mem_range.mp hi
    have hgen : Y.ring.dividedPowers.dpow (n - i) (k : Y.ring) ∈ I₂ := by
      change Y.ring.dividedPowers.dpow (n - i) (k : Y.ring) ∈
        Ideal.span {z | ∃ m, 2 ≤ m ∧ ∃ x, x ∈ diagonalKernel h ⊓ Y.ring.ideal ∧
          z = Y.ring.dividedPowers.dpow m x}
      apply Ideal.subset_span
      exact ⟨n - i, by omega, k, ⟨hkK, hkI⟩, rfl⟩
    exact I₂.mul_mem_left (Y.ring.dividedPowers.dpow i a) hgen
  have hqdp : q (Y.ring.dividedPowers.dpow n y) =
      X.ring.dividedPowers.dpow n (q y) :=
    (diagonalMap h).hom.isDPMorphism.dpow_comp y hy |>.symm
  have hs₀dp : ∀ m : ℕ, s₀.hom.toRingHom
      (X.ring.dividedPowers.dpow m (q y)) =
      Y.ring.dividedPowers.dpow m a := by
    intro m
    simpa [a] using
      (s₀.hom.isDPMorphism.dpow_comp (q y) hqy).symm
  have hrep : (diagonalClassRep h (Y.ring.dividedPowers.dpow n y) : Y.ring) =
      Y.ring.dividedPowers.dpow n y - Y.ring.dividedPowers.dpow n a := by
    change Y.ring.dividedPowers.dpow n y -
      s₀.hom.toRingHom (q (Y.ring.dividedPowers.dpow n y)) = _
    rw [hqdp, hs₀dp n]
  change ((diagonalClassRep h (Y.ring.dividedPowers.dpow n y) : Y.ring) -
      s₀.hom.toRingHom
        (X.ring.dividedPowers.dpow (n - 1) (q y)) * (k : Y.ring)) ∈
    diagonalKernel h ^ (2 : ℕ) + I₂
  rw [hrep, hs₀dp (n - 1), hcalc]
  exact Submodule.mem_sup_right htail

/-- **Stacks Project, Tag 07HV, part (1).** Let `(B, J, δ)` be an object of `CRIS(C/A)` and
`(B(1), J(1), δ(1))` its coproduct with itself in `CRIS(C/A)`, with `K = Ker(B(1) → B)`.  Then
`K ∩ J(1) ⊂ J(1)` is preserved by the divided power structure. -/
@[stacks 07HV "part (1) in CRIS(C/A): K ∩ J(1) is preserved by the divided powers"]
public theorem diagonalKernel_isSubDPIdeal
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Y.ring.dividedPowers.IsSubDPIdeal (diagonalKernel h ⊓ Y.ring.ideal) :=
  DividedPowers.isSubDPIdeal_ker Y.ring.dividedPowers
    (hJ := X.ring.dividedPowers) (diagonalMap h).hom.isDPMorphism

end DividedPowerThickening

end Crystalline

end
