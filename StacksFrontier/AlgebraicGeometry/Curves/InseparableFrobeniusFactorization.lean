module

public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.GenericDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.Topology.Dimension.IrreducibleDimensionOne

/-!
# Inseparable morphisms of curves of degree the characteristic

Let `k` be a field of characteristic `p > 0` and let `f : X ⟶ Y` be a nonconstant morphism of
proper nonsingular curves over `k` with `X` smooth. If the extension of function fields
`k(Y) ⊆ k(X)` is inseparable of degree `p`, then `Y` is the Frobenius twist of `X` and `f` is
the relative Frobenius, by a unique isomorphism over `k`.

The argument runs through function fields. A nonseparable extension of prime degree is purely
inseparable, so every `p`-th power of `k(X)` lies in `k(Y)`; hence the absolute Frobenius of
`X` factors through `f` at the generic point, which produces a rational map from `Y` to the
Frobenius twist. A normal curve maps to a proper variety as soon as it does rationally, so the
rational map is a morphism `g`, and `f ≫ g` is the relative Frobenius. Comparing degrees, `g`
has degree one, and a degree-one morphism from a proper curve to a normal curve over `k` is an
isomorphism.

## Main results

* `AlgebraicGeometry.existsUnique_iso_frobeniusTwist_of_inseparable_degree_prime`
  identifies `Y` with the Frobenius twist of `X` and `f` with the relative Frobenius.
* `AlgebraicGeometry.isIso_of_residueDegree_eq_one` states that a morphism of curves over `k`
  from a proper curve to a normal curve which has residue degree one at the generic point is
  an isomorphism in the over category.
* `AlgebraicGeometry.existsUnique_morphism_of_fromSpecStalk_genericPoint` extends a morphism
  defined at the generic point of a normal curve to the whole curve, uniquely.

## Implementation notes

Degrees of extensions of function fields are residue degrees at the generic point, so they are
expressed with `AlgebraicGeometry.Scheme.Hom.residueDegree`, and inseparability of the
extension is nonseparability of the algebra attached to the residue-field map of `f` there.
Curves and their morphisms live over `Spec k`, so the isomorphism asserted by the source is an
isomorphism in `CategoryTheory.Over (Spec (.of k))`; its compatibility with the structure
morphisms to `Spec k` is part of its type.

Comparing degrees uses only that the degree of the relative Frobenius of a smooth curve divides
`p`, which already forces the comparison morphism to have degree one and hence to be an
isomorphism; the equality of that degree with `p` comes out of the argument.

## References

* [Stacks Project, Tag 0CCY](https://stacks.math.columbia.edu/tag/0CCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- A nonconstant morphism of curves over a field is dominant: the target is an irreducible
Jacobson space of dimension one, in which a subset with two points is dense. -/
theorem isDominant_of_nontrivial_range_of_isCurve
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY]
    (f : X ⟶ Y) (hnonconstant : (Set.range f).Nontrivial) : IsDominant f := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace pY
  exact ⟨Stacks.Topology.Dimension.denseRange_of_nontrivial_of_topologicalKrullDim_eq_one
    f f.continuous hnonconstant (IsCurve.topologicalKrullDim_eq_one pY)⟩

/-- A nonseparable extension of prime degree equal to the characteristic is purely inseparable:
its separable degree divides the prime and cannot equal it. -/
theorem isPurelyInseparable_residueFieldMap_genericPoint
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] (f : X ⟶ Y)
    (hdegree : f.residueDegree (genericPoint X) = p)
    (hinseparable :
      letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
      ¬ Algebra.IsSeparable (Y.residueField (f (genericPoint X)))
          (X.residueField (genericPoint X))) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable := by
  let K := Y.residueField (f (genericPoint X))
  let L := X.residueField (genericPoint X)
  let ι := (f.residueFieldMap (genericPoint X)).hom
  let _ : Algebra K L := ι.toAlgebra
  have hdim : Module.finrank K L = p := by
    simpa [Scheme.Hom.residueDegree, ι] using hdegree
  have _ : Module.Finite K L := Module.finite_of_finrank_pos (hdim ▸ (Fact.out : p.Prime).pos)
  have hnot : ¬ Algebra.IsSeparable K L := by
    simpa [K, L, ι] using hinseparable
  have hdiv : Field.finSepDegree K L ∣ p := hdim ▸ Field.finSepDegree_dvd_finrank K L
  refine (isPurelyInseparable_iff_finSepDegree_eq_one K L).2
    (((Nat.dvd_prime Fact.out).mp hdiv).resolve_right fun hsep => hnot ?_)
  rw [← Field.finSepDegree_eq_finrank_iff K L, hsep, hdim]

/-- In a purely inseparable extension of degree the prime `p`, every `p`-th power lies in the
base field: the minimal polynomial of an element is `X ^ p ^ n - c` with `p ^ n ≤ p`. -/
private theorem pow_mem_range_of_finrank_eq_prime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    [IsPurelyInseparable F E] (hdim : Module.finrank F E = p) (x : E) :
    x ^ p ∈ (algebraMap F E).range := by
  have _ : Module.Finite F E := Module.finite_of_finrank_pos (hdim ▸ (Fact.out : p.Prime).pos)
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hle : p ^ n ≤ p := by simpa [hy, hdim] using minpoly.natDegree_le (A := F) x
  have hn : n ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    simpa using hle
  have hx : x ^ (p ^ n) = algebraMap F E y := by
    have := minpoly.aeval F x
    rw [hy] at this
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using this
  interval_cases n
  · refine ⟨y ^ p, ?_⟩
    simpa only [pow_zero, pow_one, map_pow] using congrArg (fun a : E => a ^ p) hx.symm
  · exact ⟨y, by simpa using hx.symm⟩

/-- A field homomorphism whose image contains every `p`-th power factors the Frobenius. -/
@[ega "0 22.4.8" "special case"]
theorem exists_comp_eq_frobenius_of_pow_mem_range
    {F E : Type*} [Field F] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (ι : F →+* E) (hp : ∀ x : E, x ^ p ∈ ι.range) :
    ∃ ρ : E →+* F, ι.comp ρ = frobenius E p := by
  let φ := (frobenius E p).codRestrict ι.fieldRange hp
  refine ⟨ι.rangeRestrictFieldEquiv.symm.toRingHom.comp φ, ?_⟩
  ext x
  exact congrArg Subtype.val (ι.rangeRestrictFieldEquiv.apply_symm_apply (φ x))

/-- If the extension of function fields of a dominant morphism of curves is purely inseparable
of degree `p`, then every `p`-th power of the function field of the source lies in the image of
the function field of the target. -/
theorem pow_mem_range_functionFieldMap
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] (f : X ⟶ Y) [IsDominant f]
    (hdegree : f.residueDegree (genericPoint X) = p)
    (hpure : (f.residueFieldMap (genericPoint X)).hom.IsPurelyInseparable)
    (x : X.functionField) : x ^ p ∈ (functionFieldMap f).range := by
  let K := Y.residueField (f (genericPoint X))
  let L := X.residueField (genericPoint X)
  let ι := (f.residueFieldMap (genericPoint X)).hom
  let _ : Algebra K L := ι.toAlgebra
  have _ : CharP K p := charP_residueField_of_over p pY _
  have _ : IsPurelyInseparable K L := hpure
  let eY := genericResidueEquivOfDominant f
  let eX := genericResidueEquiv X
  have hn : ι.comp eY.toRingHom = eX.toRingHom.comp (functionFieldMap f) :=
    residueFieldMap_comp_genericResidueEquivOfDominant f
  have hdim : Module.finrank K L = p := hdegree
  obtain ⟨y, hy⟩ := pow_mem_range_of_finrank_eq_prime p hdim (eX x)
  refine ⟨eY.symm y, eX.injective ?_⟩
  calc
    eX (functionFieldMap f (eY.symm y)) = ι (eY (eY.symm y)) :=
      (RingHom.congr_fun hn _).symm
    _ = (eX x) ^ p := by rwa [eY.apply_symm_apply]
    _ = eX (x ^ p) := (map_pow eX x p).symm

/-- Two morphisms in the over category out of a reduced scheme into a separated one agree as
soon as they agree after a dominant morphism. -/
theorem overHom_ext_of_isDominant
    {S : Scheme.{u}} {X Y : Over S} [IsReduced X.left] [IsSeparated Y.hom]
    {W : Scheme.{u}} (ι : W ⟶ X.left) [IsDominant ι]
    {f g : X ⟶ Y} (h : ι ≫ f.left = ι ≫ g.left) : f = g :=
  Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Y.hom (f.w.trans g.w.symm) ι h)

/-- A morphism from the spectrum of the function field of a normal curve to a proper variety
over the base field extends uniquely to the curve. -/
theorem existsUnique_morphism_of_fromSpecStalk_genericPoint
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsNormal X.left] [IsProperVariety k Y.hom]
    (g : Spec X.left.functionField ⟶ Y.left)
    (hg : g ≫ Y.hom = X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom) :
    ∃! f : X ⟶ Y, X.left.fromSpecStalk (genericPoint X.left) ≫ f.left = g := by
  have _ : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let r := Scheme.RationalMap.ofFunctionField X.hom Y.hom g hg
  have hr : r.IsOver (Spec (.of k)) := by
    rw [Scheme.RationalMap.isOver_iff]
    exact ((Scheme.RationalMap.equivFunctionField X.hom Y.hom) ⟨g, hg⟩).property
  obtain ⟨f, hf⟩ := (toRationalMap_bijective k X Y).surjective ⟨r, hr⟩
  have hfun : f.left.toRationalMap.fromFunctionField = g := by
    rw [show f.left.toRationalMap = r from congrArg Subtype.val hf]
    exact Scheme.RationalMap.fromFunctionField_ofFunctionField X.hom Y.hom g hg
  have hf₀ : X.left.fromSpecStalk (genericPoint X.left) ≫ f.left = g := by
    simpa [Scheme.PartialMap.fromFunctionField,
      Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] using hfun
  refine ⟨f, hf₀, fun f' hf' => ?_⟩
  apply (toRationalMap_bijective k X Y).injective
  apply Subtype.ext
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  change f'.left.toRationalMap.fromFunctionField = f.left.toRationalMap.fromFunctionField
  simpa [Scheme.PartialMap.fromFunctionField,
    Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] using hf'.trans hf₀.symm

/-- The spectrum of the Frobenius of a field of characteristic `p` is the absolute Frobenius of
its spectrum. -/
theorem specMap_frobenius_eq_absoluteFrobenius (K : Type u) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (h : IsInCharacteristic (Spec (.of K)) p) :
    Spec.map (CommRingCat.ofHom (frobenius K p)) = absoluteFrobenius _ p h := by
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext a
  change (Scheme.ΓSpecIso (.of K)).inv.hom (a ^ p) =
    (absoluteFrobenius _ p h).appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom a)
  rw [map_pow]
  exact (absoluteFrobenius_appLE_apply (Spec (.of K)) p h ⊤
    (by simp) ((Scheme.ΓSpecIso (.of K)).inv.hom a)).symm

/-- A morphism `γ` from the spectrum of the function field of a normal curve `Y` to a proper
variety `Z` over `k`, compatible with a morphism `h` from a curve `X` through the generic point
of `X`, gives a morphism `Y ⟶ Z` which composes with a dominant `f : X ⟶ Y` to `h`. -/
private theorem exists_comp_eq_of_functionFieldMap_fac
    {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (Z : Over (Spec (.of k))) [IsCurve k pX] [IsCurve k pY] [IsNormal Y] [IsProperVariety k Z.hom]
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ pY = pX)
    (h : X ⟶ Z.left) (hh : h ≫ Z.hom = pX)
    (γ : Spec Y.functionField ⟶ Z.left)
    (hfac : Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫ γ =
      X.fromSpecStalk (genericPoint X) ≫ h) :
    ∃ g : Over.mk pY ⟶ Z, f ≫ g.left = h := by
  have _ := surjective_specMap_of_field (functionFieldMap f)
  have hγ : γ ≫ Z.hom = Y.fromSpecStalk (genericPoint Y) ≫ pY := by
    apply ext_of_isDominant (ι := Spec.map (CommRingCat.ofHom (functionFieldMap f)))
    rw [← Category.assoc, hfac, Category.assoc, hh, ← Category.assoc _ _ pY,
      functionFieldMap_fromSpecStalk, Category.assoc, hf]
  have _ : IsCurve k (Over.mk pY).hom := inferInstanceAs (IsCurve k pY)
  have _ : IsNormal (Over.mk pY).left := inferInstanceAs (IsNormal Y)
  obtain ⟨g, hg, _⟩ := existsUnique_morphism_of_fromSpecStalk_genericPoint (Over.mk pY) Z γ hγ
  change Y.fromSpecStalk (genericPoint Y) ≫ g.left = γ at hg
  have _ : IsDominant (X.fromSpecStalk (genericPoint X)) := isDominant_fromSpecStalk_genericPoint X
  refine ⟨g, ext_of_isDominant_of_isSeparated Z.hom ((Category.assoc _ _ _).trans
    ((congrArg (f ≫ ·) (Over.w g)).trans (hf.trans hh.symm)))
    (X.fromSpecStalk (genericPoint X)) ?_⟩
  rw [← Category.assoc _ f, ← functionFieldMap_fromSpecStalk, Category.assoc, hg, hfac]

/-- A dominant morphism of curves over `k` through which every `p`-th power of the function
field of the source factors fits into a commutative triangle with the relative Frobenius: the
factorization gives a rational map to the Frobenius twist, which extends over the normal
target. -/
theorem exists_comp_eq_relativeFrobenius_of_pow_mem_range
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsNormal Y]
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ pY = pX)
    (hpow : ∀ x : X.functionField, x ^ p ∈ (functionFieldMap f).range)
    (hproper : IsProperVariety k
      ((frobeniusTwist (Spec (.of k)) p
          (Stacks.Frobenius.isInCharacteristic_of_over
            (Over.mk (𝟙 (Spec (.of k)))))).obj (Over.mk pX)).hom) :
    ∃ g : Over.mk pY ⟶ ((frobeniusTwist (Spec (.of k)) p
        (Stacks.Frobenius.isInCharacteristic_of_over
          (Over.mk (𝟙 (Spec (.of k)))))).obj (Over.mk pX)),
      f ≫ g.left =
        (relativeFrobenius (Spec (.of k)) p
          (Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k)))))
          (Over.mk pX)).left := by
  let S := Spec (.of k)
  let hS := Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 S))
  let hX := Stacks.Frobenius.isInCharacteristic_of_over (Over.mk pX)
  let T := (frobeniusTwist S p hS).obj (Over.mk pX)
  let F := (relativeFrobenius S p hS (Over.mk pX)).left
  let ηX := X.fromSpecStalk (genericPoint X)
  let ηY := Y.fromSpecStalk (genericPoint Y)
  let φ := functionFieldMap f
  have _ : CharP (X.residueField (genericPoint X)) p := charP_residueField_of_over p pX _
  have hcp : CharP X.functionField p :=
    ((genericResidueEquiv X).toRingHom.charP_iff_charP p).mpr inferInstance
  obtain ⟨ρ, hρ⟩ := exists_comp_eq_frobenius_of_pow_mem_range p φ hpow
  let φSpec := Spec.map (CommRingCat.ofHom φ)
  let γ := Spec.map (CommRingCat.ofHom ρ) ≫ ηX
  have hφ : φSpec ≫ ηY = ηX ≫ f := functionFieldMap_fromSpecStalk f
  have hγ : φSpec ≫ γ = ηX ≫ absoluteFrobenius X p hX := by
    dsimp only [φSpec, γ]
    rw [← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom (φ.comp ρ)) ≫ ηX = _
    rw [hρ, specMap_frobenius_eq_absoluteFrobenius X.functionField p
      (@Stacks.Frobenius.isInCharacteristic_of_over X.functionField _ p hcp
        (Over.mk (𝟙 (Spec X.functionField))))]
    exact absoluteFrobenius_naturality ηX p _ hX
  have _ : Surjective φSpec := surjective_specMap_of_field φ
  have hbase : γ ≫ pX = (ηY ≫ pY) ≫ absoluteFrobenius S p hS := by
    apply ext_of_isDominant (ι := φSpec)
    rw [← Category.assoc, hγ, Category.assoc, absoluteFrobenius_naturality pX p hX hS]
    simp only [← Category.assoc, hφ]
    rw [Category.assoc ηX f, hf]
  let γT : Spec Y.functionField ⟶ T.left := Limits.pullback.lift γ (ηY ≫ pY) hbase
  have := hproper
  exact exists_comp_eq_of_functionFieldMap_fac pX pY T f hf F
    (relativeFrobenius_snd S p hS (Over.mk pX)) γT (by
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, γT, Limits.pullback.lift_fst, F, relativeFrobenius_fst]
        exact hγ
      · simp only [Category.assoc, γT, Limits.pullback.lift_snd, F, relativeFrobenius_snd]
        rw [← Category.assoc, hφ]
        simp only [Category.assoc, hf]
        rfl)

/-- A dominant morphism over `k` from a proper curve to a normal curve whose residue degree at
the generic point is one is an isomorphism: the extension of function fields is a bijection, so
the inverse extends to a morphism inverse to it. -/
theorem isIso_of_residueDegree_eq_one
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsCurve k Y.hom] [IsProper X.hom] [IsNormal Y.left]
    (f : X ⟶ Y) [IsDominant f.left]
    (hdegree : f.left.residueDegree (genericPoint X.left) = 1) : IsIso f := by
  let ηX := X.left.fromSpecStalk (genericPoint X.left)
  let ηY := Y.left.fromSpecStalk (genericPoint Y.left)
  let φ := functionFieldMap f.left
  let e := RingEquiv.ofBijective φ
    (functionFieldMap_bijective_of_residueDegree_eq_one f.left hdegree)
  let φSpec := Spec.map (CommRingCat.ofHom φ)
  let γ := Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ ηX
  have hφ : φSpec ≫ ηY = ηX ≫ f.left := functionFieldMap_fromSpecStalk f.left
  have hγ : φSpec ≫ γ = ηX := by
    dsimp only [φSpec, γ]
    rw [← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom φ = 𝟙 _ := by
      ext x
      exact e.apply_symm_apply x
    rw [he, Spec.map_id, Category.id_comp]
  have _ : IsProperVariety k X.hom := IsProperVariety.mk
  obtain ⟨g, hg⟩ := exists_comp_eq_of_functionFieldMap_fac X.hom Y.hom X f.left f.w (𝟙 _)
    (Category.id_comp _) γ (hγ.trans (Category.comp_id _).symm)
  have hfg : f ≫ g = 𝟙 X := Over.OverMorphism.ext hg
  have hgf : g ≫ f = 𝟙 Y := by
    apply overHom_ext_of_isDominant f.left
    change f.left ≫ (g.left ≫ f.left) = f.left ≫ 𝟙 Y.left
    rw [← Category.assoc, show f.left ≫ g.left = 𝟙 X.left from
      congrArg (fun t : X ⟶ X => t.left) hfg, Category.id_comp, Category.comp_id]
  exact ⟨⟨g, hfg, hgf⟩⟩

/-- **Stacks Project, Tag 0CCY.** A nonconstant morphism of proper nonsingular curves over a
field of characteristic `p`, with smooth source, whose extension of function fields is
inseparable of degree `p`, is the relative Frobenius up to a unique isomorphism of its target
with the Frobenius twist of its source. -/
@[stacks 0CCY]
theorem existsUnique_iso_frobeniusTwist_of_inseparable_degree_prime
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
    (_hXreg : IsRegular X) (hYreg : IsRegular Y)
    [Smooth pX] (f : X ⟶ Y) (_hf : f ≫ pY = pX)
    (hnonconstant : (Set.range f).Nontrivial)
    (hdegree : f.residueDegree (genericPoint X) = p)
    (hinseparable :
      letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
      ¬ Algebra.IsSeparable
          (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X))) :
    ∃! i : Over.mk pY ≅
        (frobeniusTwist (Spec (.of k)) p
          (Stacks.Frobenius.isInCharacteristic_of_over
            (Over.mk (𝟙 (Spec (.of k)))))).obj (Over.mk pX),
      f ≫ i.hom.left =
        (relativeFrobenius (Spec (.of k)) p
          (Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k)))))
          (Over.mk pX)).left := by
  classical
  let S := Spec (.of k)
  let hS := Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 S))
  let T := (frobeniusTwist S p hS).obj (Over.mk pX)
  let F := (relativeFrobenius S p hS (Over.mk pX)).left
  have _ : IsDominant f := isDominant_of_nontrivial_range_of_isCurve pX pY f hnonconstant
  have _ : IsNormal Y := isNormal_of_isRegular Y hYreg
  have _ : Smooth T.hom := by
    change Smooth (Limits.pullback.snd pX (absoluteFrobenius S p hS))
    infer_instance
  have _ : IsProper T.hom := by
    change IsProper (Limits.pullback.snd pX (absoluteFrobenius S p hS))
    infer_instance
  have _ : IsNormal T.left :=
    isNormal_of_isRegular T.left (isRegular_of_smooth_over_field T.hom)
  have _ : ∀ x : T.left, _root_.IsReduced (T.left.presheaf.stalk x) := fun x => inferInstance
  have hred : IsReduced T.left := isReduced_of_isReduced_stalk T.left
  have _ : IsVariety k T.hom := isVariety_frobeniusTwist_of_isReduced pX p hred
  have hh : IsHomeomorph F := (relativeFrobenius_universalHomeomorphism S p hS
    (Over.mk pX)).universally_isHomeomorph _ _ _ CategoryTheory.IsPullback.of_id_snd
  have _ : IsCurve k T.hom :=
    { toIsVariety := inferInstance
      topologicalKrullDim_eq_one :=
        (IsHomeomorph.topologicalKrullDim_eq F hh).symm.trans
          (IsCurve.topologicalKrullDim_eq_one pX) }
  have hproper : IsProperVariety k T.hom := IsProperVariety.mk
  have hpure := isPurelyInseparable_residueFieldMap_genericPoint p pX pY f hdegree hinseparable
  obtain ⟨g, hg⟩ := exists_comp_eq_relativeFrobenius_of_pow_mem_range p pX pY f _hf
    (pow_mem_range_functionFieldMap p pX pY f hdegree hpure) hproper
  change f ≫ g.left = F at hg
  have _ : IsDominant (f ≫ g.left) := by
    rw [hg]
    exact ⟨hh.surjective.denseRange⟩
  have _ : IsDominant g.left := IsDominant.of_comp f g.left
  have hFdvd : F.residueDegree (genericPoint X) ∣ p ^ 1 :=
    residueDegree_relativeFrobenius_genericPoint_dvd pX p hS 1
      (IsCurve.topologicalKrullDim_eq_one pX)
  have hdeg : g.left.residueDegree (genericPoint Y) = 1 := by
    have hm := residueDegree_comp f g.left (genericPoint X)
    rw [hg, hdegree, map_genericPoint_of_isDominant f] at hm
    rw [pow_one, hm] at hFdvd
    exact Nat.dvd_one.mp
      (Nat.dvd_of_mul_dvd_mul_right (Fact.out : p.Prime).pos (by rwa [one_mul]))
  have _ : IsCurve k (Over.mk pY).hom := inferInstanceAs (IsCurve k pY)
  have _ : IsProper (Over.mk pY).hom := inferInstanceAs (IsProper pY)
  have _ : IsIso g := isIso_of_residueDegree_eq_one (Over.mk pY) T g hdeg
  exact ⟨asIso g, hg, fun i hi => Iso.ext (overHom_ext_of_isDominant f (hi.trans hg.symm))⟩

end AlgebraicGeometry

end
