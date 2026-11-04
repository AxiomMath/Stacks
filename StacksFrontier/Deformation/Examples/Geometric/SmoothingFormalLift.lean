module

public import StacksFrontier.Deformation.Examples.Geometric.CurveIsolatedSingularities
public import StacksFrontier.Deformation.Examples.Geometric.RingsHull
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFormalObject
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective
public import StacksFrontier.Deformation.Smooth.Pi

/-!
# Lifting the local smoothings to a formal deformation of a curve

Let `X` be a separated scheme of finite type over a field `k` with `dim X ≤ 1`, smooth over `k`
away from finitely many closed points `p_i`. Given, for each `i`, a flat `k⟦t⟧`-algebra `B_i` with
`B_i / tB_i ≅ 𝒪_{X, p_i}`, there is a formal deformation `ξ` of `X` over `k⟦t⟧` whose image in
`∏ Def_{𝒪_{X, p_i}}` is isomorphic to the formal object `(B_i / 𝔪^{n+1} B_i)`. This is the step of
the proof of [Stacks, Tag 0E7Y] which reads "By Lemma 0DZP the map `Def_X → ∏ Def_{𝒪_{X,p_i}}` is
a smooth map between deformation categories. Hence by Formal Deformation Theory, Lemma 06HN there
exists a formal object `(X_n)` in `Def_X` mapping to the formal object `∏ (B_i/t^n)`."

## Main definitions

* `Deformation.Examples.Smoothing.trivialDeformation`: `X` itself, as a deformation of `X` over the
  residue field object of `𝒞_k`.

## Main results

* `Deformation.Examples.Smoothing.essSurj_fiberFunctor_localRingFunctors`: the fibre over the
  residue field of `Def_X → ∏ Def_{𝒪_{X,p_i}}` is essentially surjective, the target being a
  predeformation category.
* `Deformation.Examples.Smoothing.exists_formalObject_iso_piFormalObject`: the formal deformation.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0DZP](https://stacks.math.columbia.edu/tag/0DZP)
* [Stacks Project, Tag 06HN](https://stacks.math.columbia.edu/tag/06HN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples.Smoothing

variable {k : Type u} [Field k]

/-- The closed point of the spectrum of the residue field object is an isomorphism. -/
instance isIso_residueSpecMap_residueFieldObject :
    IsIso (residueSpecMap (residueFieldObject.{u, u, u} k k)) := by
  have hbij :
      Function.Bijective (Deformation.Artin.residueMap (residueFieldObject.{u, u, u} k k)) := by
    refine ⟨fun a b h => ?_, fun c => ⟨ULift.up c, ?_⟩⟩
    · have ha := residueFieldObject_residue.{u, u, u} k k a
      have hb := residueFieldObject_residue.{u, u, u} k k b
      have h' : a.down = b.down := by
        rw [← ha, ← hb]
        exact h
      exact ULift.ext _ _ h'
    · exact residueFieldObject_residue.{u, u, u} k k (ULift.up.{u, u} c)
  have : IsIso (CommRingCat.ofHom (Deformation.Artin.residueMap
      (residueFieldObject.{u, u, u} k k))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact inferInstanceAs (IsIso (Spec.map _))

/-- **The trivial deformation.** A scheme `X` over `k` is a deformation of itself over the residue
field object of `𝒞_k`. -/
def trivialDeformation (X : Over (Spec (.of k))) :
    SchemeDeformationCategory (Λ := k) (k := k) X where
  base := residueFieldObject k k
  scheme := X.left
  toBase := X.hom ≫ residueSpecMap (residueFieldObject k k)
  flat := by
    have : Flat X.hom := inferInstance
    infer_instance
  specialMap := 𝟙 X.left
  specialCartesian := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Any two objects of the fibre of a predeformation category over the residue field are
isomorphic. -/
theorem nonempty_iso_of_isPredeformationCategory {F : Type*} [Category F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} k k} (hp : IsPredeformationCategory p)
    (a b : p.Fiber (residueFieldObject k k)) : Nonempty (a ≅ b) := by
  obtain ⟨e⟩ := hp.specialFiber
  exact ⟨e.fullyFaithfulFunctor.preimageIso (eqToIso (Subsingleton.elim _ _))⟩

section Curve

variable (X : Over (Spec (.of k))) {ι : Type u} (p : ι → X.left)

/-- The fibre over the residue field of `Def_X → ∏ Def_{𝒪_{X, p_i}}` is essentially surjective:
the target is a predeformation category, so its fibre over `k` has a single isomorphism class,
and the trivial deformation of `X` lies over `k`. -/
theorem essSurj_fiberFunctor_localRingFunctors :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    (fiberFunctor (localRingFunctors (Λ := k) X p) (residueFieldObject k k)).EssSurj := by
  let : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  have hpre : IsPredeformationCategory
      (piBasedCategory fun i => ringDeformationBasedCategory k k
        (X.left.presheaf.stalk (p i))).p :=
    piBasedCategory_isPredeformationCategory _ fun i =>
      isPredeformationCategory_ringDeformationProjection (Λ := k) (k := k) _
  refine ⟨fun y => ?_⟩
  let x₀ : (schemeDeformationCategoryOver k k X).p.Fiber (residueFieldObject k k) :=
    ⟨trivialDeformation X, rfl⟩
  exact ⟨x₀, nonempty_iso_of_isPredeformationCategory hpre _ y⟩

attribute [local instance 100] henselizationAlgebra in
/-- **The formal deformation of the curve.** Under the hypotheses of Stacks 0DZP, for any family of
flat `k⟦t⟧`-algebras `B_i` with `B_i / tB_i ≅ 𝒪_{X, p_i}`, there is a formal object `ξ` of `Def_X`
over a complete local `k`-algebra whose image in `∏ Def_{𝒪_{X, p_i}}` is isomorphic to the formal
object `(B_i / 𝔪^{n+1} B_i)` of `Deformation.Examples.Smoothing.piFormalObject`. -/
theorem exists_formalObject_iso_piFormalObject [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (hdim : topologicalKrullDim (X.left : Type u) ≤ 1) [Finite ι]
    (hinj : Function.Injective p) (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hsm : ∀ x : X.left, x ∉ Set.range p → x ∈ X.hom.smoothLocus)
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra (PowerSeries k) (B i)]
    [∀ i, Module.Flat (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
    [∀ i, IsScalarTower k (PowerSeries k) (B i)] :
    letI : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
    ∀ e : ∀ i, (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X.left.presheaf.stalk (p i),
      ∃ ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X),
        Nonempty ((completionMap (localRingFunctors (Λ := k) X p)).obj ξ ≅
          piFormalObject k B (fun i => X.left.presheaf.stalk (p i)) e) := by
  let : ∀ i, Algebra k (X.left.presheaf.stalk (p i)) := fun i => stalkAlgebraOver X (p i)
  intro e
  have hφ := (isSmooth_localRingFunctors_and_chain (Λ := k) X p hdim hinj hclosed hsm).1
  have hq := isCofiberedInGroupoids_pi_ringDeformation (Λ := k) (k := k)
    fun i => X.left.presheaf.stalk (p i)
  have hsurj := completionMap_essSurj_of_isSmooth_of_fiber_essSurj
    (localRingFunctors (Λ := k) X p) hq hφ (essSurj_fiberFunctor_localRingFunctors X p)
  obtain ⟨ξ, ⟨m⟩⟩ :=
    hsurj.mem_essImage (piFormalObject k B (fun i => X.left.presheaf.stalk (p i)) e)
  exact ⟨ξ, ⟨m⟩⟩

end Curve

end Deformation.Examples.Smoothing

end
