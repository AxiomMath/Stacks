module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StandardCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# The big affine h site

Let `B` be a big h site containing a scheme `S`.  The affine objects of the big h category
over `S` form the big affine h category, whose covering families are those which cover in
the big h site over `S` and are standard h coverings.  This file proves that these families
satisfy the site axioms: an isomorphism covers, covering families compose, and a covering
family base changes to a covering family.

## Main results

* `AlgebraicGeometry.BigAffineH.isSite`: the standard h covering families of affine objects
  over `S` satisfy the isomorphism, composition and base change axioms.

## Implementation notes

Each axiom is obtained from the corresponding axiom of the ambient big h site, whose covering
families already carry the h-covering condition.  What has to be added is the standard h
condition, and over an affine base that is exactly the h-covering condition together with
finiteness of the index type, affineness of the sources and finite presentation of the
members, by `AlgebraicGeometry.isStandardHCovering_of_isHCovering`.  The h-covering condition
is read off the ambient site's conclusion, so only the three bookkeeping conditions are
checked by hand.

The fibre product of the base change axiom is produced by the ambient site; its source is
affine because the comparison isomorphism with the fibre product taken in all schemes is an
isomorphism of schemes, and a fibre product of affine schemes over an affine base is affine.
Fibre products exist in the size-bounded category of schemes by Stacks 021U, so the
projections of the ambient site's square really do present a fibre product there.

## References

* [Stacks Project, Tag 0EU2](https://stacks.math.columbia.edu/tag/0EU2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 0EU2.** The standard h covering families of the affine objects of the big h
category over `S` satisfy the site axioms. -/
@[stacks 0EU2]
public lemma BigAffineH.isSite (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsSite (BigAffineH.IsCovering B S hS) := by
  let G := BigAffineH.inclusion B S hS ⋙ BigHOver.forget B S hS
  let K := BigAffineH.toScheme B S hS
  obtain ⟨hIso, hComp, hBC⟩ := B.isSite
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    have hcov := hIso (G.map f)
    change B.IsCovering ⟨G.obj U, (PreZeroHypercover.singleton.{u + 1} f).map G⟩ at hcov
    refine ⟨hcov, ?_⟩
    show AlgebraicGeometry.IsStandardHCovering (fun _ : PUnit.{u + 2} ↦ K.map f)
    exact isStandardHCovering_of_isHCovering inferInstance (fun _ ↦ inferInstance)
      (fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩) hcov.h
  · intro E hE F hF h
    change B.IsCovering ⟨G.obj E.1, E.2.map G⟩ ∧
      AlgebraicGeometry.IsStandardHCovering (fun i ↦ K.map (E.2.f i)) at hE
    change ∀ i, B.IsCovering ⟨G.obj (F i).1, (F i).2.map G⟩ ∧
      AlgebraicGeometry.IsStandardHCovering (fun j ↦ K.map ((F i).2.f j)) at hF
    have hc := hComp ⟨G.obj E.1, E.2.map G⟩ hE.1
      (fun i ↦ ⟨G.obj (F i).1, (F i).2.map G⟩) (fun i ↦ (hF i).1)
      (fun i ↦ congrArg G.obj (h i))
    have hcov : B.IsCovering ⟨G.obj E.1,
        (E.2.bind fun i ↦ (F i).2.pushforward (eqToHom (h i))).map G⟩ := by
      convert hc using 1
      simp [G, PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward]
    have : Finite E.2.I₀ := hE.2.1
    have : ∀ i, Finite (F i).2.I₀ := fun i ↦ (hF i).2.1
    have hfin : Finite (Σ i : E.2.I₀, (F i).2.I₀) := inferInstance
    refine ⟨hcov, isStandardHCovering_of_isHCovering hfin (fun s ↦ (hF s.1).2.2.1 s.2)
      (fun s ↦ ?_) hcov.h⟩
    obtain ⟨_, _, _⟩ := (hF s.1).2.2.2.1 s.2
    obtain ⟨_, _, _⟩ := hE.2.2.2.1 s.1
    show FinitePresentation
      (K.map ((F s.1).2.f s.2 ≫ eqToHom (h s.1)) ≫ K.map (E.2.f s.1))
    rw [Functor.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro E hE V g
    change B.IsCovering ⟨G.obj E.1, E.2.map G⟩ ∧
      AlgebraicGeometry.IsStandardHCovering (fun i ↦ K.map (E.2.f i)) at hE
    obtain ⟨P, π₁, π₂, hpb, hcov⟩ := hBC ⟨G.obj E.1, E.2.map G⟩ hE.1 (G.obj V) (G.map g)
    change E.2.I₀ → B.Schemes at P
    change ∀ i, P i ⟶ G.obj (E.2.X i) at π₁
    change ∀ i, P i ⟶ G.obj V at π₂
    change ∀ i, IsPullback (π₁ i) (π₂ i) (G.map (E.2.f i)) (G.map g) at hpb
    change B.IsCovering ⟨G.obj V, ⟨E.2.I₀, P, π₂⟩⟩ at hcov
    have hpbScheme (i : E.2.I₀) : IsPullback (B.inclusion.map (π₁ i))
        (B.inclusion.map (π₂ i)) (K.map (E.2.f i)) (K.map g) := by
      simpa [K, G] using (hpb i).map B.inclusion
    have hAff (i : E.2.I₀) : IsAffine (B.inclusion.obj (P i)) := by
      have : IsAffine (pullback (K.map (E.2.f i)) (K.map g)) := inferInstance
      exact IsAffine.of_isIso (hpbScheme i).isoPullback.hom
    let U₀ := (BigAffineH.inclusion B S hS).obj E.1
    let V₀ := (BigAffineH.inclusion B S hS).obj V
    let X₀ (i : E.2.I₀) := (BigAffineH.inclusion B S hS).obj (E.2.X i)
    let Q₀ (i : E.2.I₀) : BigHOver B S hS := Over.mk (π₂ i ≫ V₀.hom)
    let Q (i : E.2.I₀) : BigAffineH B S hS := ⟨Q₀ i, hAff i⟩
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk (Over.homMk (X := B.obj S hS) (U := Q₀ i) (V := X₀ i)
        (π₁ i) (by
          show π₁ i ≫ (X₀ i).hom = (Q₀ i).hom
          simpa [G, U₀, V₀, X₀, Q₀, Category.assoc] using
            congrArg (fun t ↦ t ≫ U₀.hom) (hpb i).w))
    let q₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk
        (Over.homMk (X := B.obj S hS) (U := Q₀ i) (V := V₀) (π₂ i) (by simp [Q₀]))
    refine ⟨Q, q₁, q₂, fun i ↦ ?_, ?_⟩
    · apply IsPullback.of_map_of_faithful (F := BigAffineH.inclusion B S hS)
      apply IsPullback.of_map_of_faithful (F := BigHOver.forget B S hS)
      simpa [G, Q, Q₀, q₁, q₂, U₀, V₀, X₀] using hpb i
    · have hcov' : B.IsCovering ⟨G.obj V, (⟨E.2.I₀, Q, q₂⟩ :
        PreZeroHypercover.{u + 1} V).map G⟩ := hcov
      refine ⟨hcov', isStandardHCovering_of_isHCovering hE.2.1 hAff (fun i ↦ ?_) hcov'.h⟩
      obtain ⟨_, _, _⟩ := hE.2.2.2.1 i
      refine ⟨?_, ?_, ?_⟩ <;>
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpbScheme i) ‹_›

end AlgebraicGeometry
