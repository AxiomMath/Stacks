module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
public import StacksFrontier.RingTheory.ZariskisMainTheorem

/-!
# Common refinements of finite-open factorizations

Any two finite-open factorizations of a quasi-finite algebra `A → T` are dominated by a third
one: the tensor product of the two intermediate algebras is finite over `A` and maps to `T`,
Zariski's main theorem produces a finite subalgebra of `T` over it through which `T` is an open
immersion, and that subalgebra embeds in `T`. Iterating gives a factorization dominating four
given ones, which is what the comparison of dualizing modules over a product needs.

## Main definitions

* `Stacks.Discriminant.finiteOpenFactorizationAbove` produces a finite-open factorization above
  a given finite subalgebra, together with the map from that subalgebra.
* `Stacks.Discriminant.commonFiniteOpenRefinement` refines two finite-open factorizations.
* `Stacks.Discriminant.CommonFiniteOpenRefinementFour` packages a refinement of four
  factorizations, constructed by `Stacks.Discriminant.commonFiniteOpenRefinementFour`.

## Implementation notes

The refinements produced here have their intermediate algebra in the same universe as the target,
because they are built as subalgebras of it. The compatibility data is recorded as the equations
`algebraMap H.middle T (r x) = algebraMap F.middle T x` together with injectivity of
`algebraMap H.middle T`, which is the form in which
`Stacks.Discriminant.dualizingModuleEquiv_tmul` consumes a common refinement.

## References

* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
-/

@[expose] public section

universe u v w x y z

namespace Stacks.Discriminant

open scoped TensorProduct

/-- Over a finite subalgebra `C` of the base through which `B` is quasi-finite of finite type,
Zariski's main theorem gives a finite-open factorization of `A → B` whose intermediate algebra
receives `C` and embeds in `B`. -/
noncomputable def finiteOpenFactorizationAbove
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [Module.Finite A C] [Algebra.FiniteType C B] [Algebra.QuasiFinite C B] :
    Σ H : FiniteOpenFactorization.{u, v, v} A B,
      {r : C →ₐ[A] H.middle //
        (∀ c, algebraMap H.middle B (r c) = algebraMap C B c) ∧
          Function.Injective (algebraMap H.middle B)} := by
  let hExist := quasiFinite_exists_finite_subalgebra (R := C) (S := B)
  let S := Classical.choose hExist
  obtain ⟨-, hfin, hopen, haway⟩ := Classical.choose_spec hExist
  letI : Algebra C S := inferInstance
  letI : Algebra A S := ((algebraMap C S).comp (algebraMap A C)).toAlgebra
  letI : Algebra S B := S.val.toRingHom.toAlgebra
  letI : IsScalarTower A C S := .of_algebraMap_eq fun a => rfl
  have hTower : IsScalarTower A S B := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C B, IsScalarTower.algebraMap_apply C S B,
      IsScalarTower.algebraMap_apply A C S]
  letI : IsScalarTower A S B := hTower
  have hfinite : Module.Finite A S := Module.Finite.trans C S
  refine ⟨⟨S, inferInstance, inferInstance, inferInstance, hTower,
    hfinite, ?_, ?_⟩, ⟨(Algebra.ofId C S).restrictScalars A, ?_⟩⟩
  · simpa only [RingHom.algebraMap_toAlgebra] using hopen
  · exact fun g hg => by simpa only [RingHom.algebraMap_toAlgebra] using haway g hg
  · exact ⟨fun c => by simp [RingHom.algebraMap_toAlgebra], fun _ _ => Subtype.ext⟩

/-- Two finite-open factorizations of a quasi-finite algebra admit a common refinement whose
intermediate algebra embeds in the target. -/
noncomputable def commonFiniteOpenRefinement
    {A : Type u} {T : Type v}
    [CommRing A] [CommRing T]
    [Algebra A T]
    [Algebra.QuasiFinite A T]
    (F : FiniteOpenFactorization.{u, v, w} A T)
    (G : FiniteOpenFactorization.{u, v, x} A T) :
    Σ H : FiniteOpenFactorization.{u, v, v} A T,
      {rs : (F.middle →ₐ[A] H.middle) × (G.middle →ₐ[A] H.middle) //
        (∀ x, algebraMap H.middle T (rs.1 x) = algebraMap F.middle T x) ∧
        (∀ x, algebraMap H.middle T (rs.2 x) = algebraMap G.middle T x) ∧
        Function.Injective (algebraMap H.middle T)} := by
  letI : CommRing F.middle := F.commRingMiddle
  letI : Algebra A F.middle := F.algebraMiddle
  letI : CommRing G.middle := G.commRingMiddle
  letI : Algebra A G.middle := G.algebraMiddle
  letI : Algebra F.middle T := F.algebraTarget
  letI : Algebra G.middle T := G.algebraTarget
  letI : IsScalarTower A F.middle T := F.scalarTower
  letI : IsScalarTower A G.middle T := G.scalarTower
  letI : Algebra.FiniteType A T := finiteType_of_finiteOpenFactorization F
  let fF : F.middle →ₐ[A] T :=
    { toRingHom := algebraMap F.middle T
      commutes' := fun a => (IsScalarTower.algebraMap_apply A F.middle T a).symm }
  let fG : G.middle →ₐ[A] T :=
    { toRingHom := algebraMap G.middle T
      commutes' := fun a => (IsScalarTower.algebraMap_apply A G.middle T a).symm }
  let K := F.middle ⊗[A] G.middle
  let iF : F.middle →ₐ[A] K := Algebra.TensorProduct.includeLeft
  let iG : G.middle →ₐ[A] K := Algebra.TensorProduct.includeRight
  let f : K →ₐ[A] T := Algebra.TensorProduct.lift fF fG fun _ _ => Commute.all _ _
  letI : Algebra A K := inferInstance
  letI : Algebra K T := f.toRingHom.toAlgebra
  letI : IsScalarTower A K T := .of_algebraMap_eq fun a => (f.commutes a).symm
  letI : Module.Finite A F.middle := F.finite_middle
  letI : Module.Finite A G.middle := G.finite_middle
  letI : Module.Finite A K := inferInstance
  letI : Algebra.FiniteType K T := Algebra.FiniteType.of_restrictScalars_finiteType A K T
  letI : Algebra.QuasiFinite K T := Algebra.QuasiFinite.of_restrictScalars A K T
  let h := finiteOpenFactorizationAbove (A := A) (B := T) (C := K)
  refine ⟨h.1, ⟨(h.2.1.comp iF, h.2.1.comp iG), fun x => ?_, fun x => ?_, h.2.2.2⟩⟩
  · exact (h.2.2.1 (iF x)).trans <| DFunLike.congr_fun
      (Algebra.TensorProduct.lift_comp_includeLeft fF fG fun _ _ => Commute.all _ _) x
  · exact (h.2.2.1 (iG x)).trans <| DFunLike.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight' fF fG fun _ _ => Commute.all _ _) x

/-- A finite-open factorization dominating four given ones, with the four comparison maps, their
compatibility with the maps to the target, and injectivity of its own map to the target. -/
structure CommonFiniteOpenRefinementFour
    {A : Type u} {T : Type v}
    [CommRing A] [CommRing T] [Algebra A T]
    (F₀ : FiniteOpenFactorization.{u, v, w} A T)
    (F₁ : FiniteOpenFactorization.{u, v, x} A T)
    (F₂ : FiniteOpenFactorization.{u, v, y} A T)
    (F₃ : FiniteOpenFactorization.{u, v, z} A T) where
  /-- The refining finite-open factorization. -/
  factorization : FiniteOpenFactorization.{u, v, v} A T
  /-- The comparison map from the middle algebra of `F₀` to that of the refinement. -/
  map₀ : F₀.middle →ₐ[A] factorization.middle
  /-- The comparison map from the middle algebra of `F₁` to that of the refinement. -/
  map₁ : F₁.middle →ₐ[A] factorization.middle
  /-- The comparison map from the middle algebra of `F₂` to that of the refinement. -/
  map₂ : F₂.middle →ₐ[A] factorization.middle
  /-- The comparison map from the middle algebra of `F₃` to that of the refinement. -/
  map₃ : F₃.middle →ₐ[A] factorization.middle
  /-- `map₀` is compatible with the maps to `T`. -/
  compat₀ : ∀ x, algebraMap factorization.middle T (map₀ x) = algebraMap F₀.middle T x
  /-- `map₁` is compatible with the maps to `T`. -/
  compat₁ : ∀ x, algebraMap factorization.middle T (map₁ x) = algebraMap F₁.middle T x
  /-- `map₂` is compatible with the maps to `T`. -/
  compat₂ : ∀ x, algebraMap factorization.middle T (map₂ x) = algebraMap F₂.middle T x
  /-- `map₃` is compatible with the maps to `T`. -/
  compat₃ : ∀ x, algebraMap factorization.middle T (map₃ x) = algebraMap F₃.middle T x
  /-- The map from the middle algebra of the refinement to `T` is injective. -/
  injective : Function.Injective (algebraMap factorization.middle T)

/-- Four finite-open factorizations of a quasi-finite algebra admit a common refinement, obtained
by refining two at a time. -/
noncomputable def commonFiniteOpenRefinementFour
    {A : Type u} {T : Type v}
    [CommRing A] [CommRing T] [Algebra A T] [Algebra.QuasiFinite A T]
    (F₀ : FiniteOpenFactorization.{u, v, w} A T)
    (F₁ : FiniteOpenFactorization.{u, v, x} A T)
    (F₂ : FiniteOpenFactorization.{u, v, y} A T)
    (F₃ : FiniteOpenFactorization.{u, v, z} A T) :
    CommonFiniteOpenRefinementFour F₀ F₁ F₂ F₃ := by
  letI : CommRing F₀.middle := F₀.commRingMiddle
  letI : Algebra A F₀.middle := F₀.algebraMiddle
  letI : CommRing F₁.middle := F₁.commRingMiddle
  letI : Algebra A F₁.middle := F₁.algebraMiddle
  letI : CommRing F₂.middle := F₂.commRingMiddle
  letI : Algebra A F₂.middle := F₂.algebraMiddle
  letI : CommRing F₃.middle := F₃.commRingMiddle
  letI : Algebra A F₃.middle := F₃.algebraMiddle
  let h₀₁ := commonFiniteOpenRefinement F₀ F₁
  let h₀₁₂ := commonFiniteOpenRefinement h₀₁.1 F₂
  let h := commonFiniteOpenRefinement h₀₁₂.1 F₃
  exact ⟨h.1,
    h.2.1.1.comp (h₀₁₂.2.1.1.comp h₀₁.2.1.1),
    h.2.1.1.comp (h₀₁₂.2.1.1.comp h₀₁.2.1.2),
    h.2.1.1.comp h₀₁₂.2.1.2,
    h.2.1.2,
    fun x => (h.2.2.1 (h₀₁₂.2.1.1 (h₀₁.2.1.1 x))).trans
      ((h₀₁₂.2.2.1 (h₀₁.2.1.1 x)).trans (h₀₁.2.2.1 x)),
    fun x => (h.2.2.1 (h₀₁₂.2.1.1 (h₀₁.2.1.2 x))).trans
      ((h₀₁₂.2.2.1 (h₀₁.2.1.2 x)).trans (h₀₁.2.2.2.1 x)),
    fun x => (h.2.2.1 (h₀₁₂.2.1.2 x)).trans (h₀₁₂.2.2.2.1 x),
    h.2.2.2.1, h.2.2.2.2⟩

end Stacks.Discriminant
