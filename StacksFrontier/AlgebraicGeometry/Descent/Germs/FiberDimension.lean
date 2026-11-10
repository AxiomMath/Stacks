module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberLocalRingDimension

/-!
# The dimension of a fibre at a point is étale local

For a morphism of germs of schemes, the dimension of its scheme-theoretic fibre at the
distinguished point is unchanged by étale changes of the source and the target germ.

## Main definitions

* `AlgebraicGeometry.HasFiberDimensionAt` says that the fibre of a morphism of germs has a
  given dimension at its distinguished point.

## Main results

* `AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget` states that this property
  is étale local on the source and the target.

## Implementation notes

A representative of the morphism of germs is a morphism of schemes defined near the
distinguished source point, hence has a scheme-theoretic fibre with a canonical point on it.
The property is the existence of a representative with the given dimension, so no
representative has to be chosen. The dimension parameter lies in `ℕ∞`, as in the source; the
ambient topological dimension type also has a bottom element for empty spaces.

Invariance is reduced to the scheme-level statement that the induced morphism of fibres in a
commutative square with étale vertical arrows is étale, and hence preserves the local
dimension. A commutative square of germs is realised on a common open neighbourhood of the
distinguished point, on which the two composites of representatives agree.

## References

* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
-/

@[expose] public section

universe u


namespace AlgebraicGeometry

open CategoryTheory
open MorphismOfGerms

private theorem fiberDimension_cast_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {y z : Y} (e : y = z) (x : f.fiber y) :
    topologicalKrullDimAt (f.fiber z)
        (cast (congrArg (fun Z : Scheme.{u} => (Z : Type u))
          (congrArg f.fiber e)) x) =
      topologicalKrullDimAt (f.fiber y) x := by
  cases e
  rfl

private theorem fiberι_cast_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {y z : Y} (e : y = z) (x : f.fiber y) :
    f.fiberι z
        (cast (congrArg (fun Z : Scheme.{u} => (Z : Type u))
          (congrArg f.fiber e)) x) = f.fiberι y x := by
  cases e
  rfl

private theorem fiberDimension_eq_of_etaleSquare
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V)
    (h' : U' ⟶ V') (h : U ⟶ V) (comm : a ≫ h = h' ≫ b)
    [Etale a] [Etale b] (x : U') :
    topologicalKrullDimAt (h.fiber (h (a x))) (h.asFiber (a x)) =
      topologicalKrullDimAt (h'.fiber (h' x)) (h'.asFiber x) := by
  have hbase : h (a x) = b (h' x) := congrArg (fun f : U' ⟶ V => f x) comm
  let φ := fiberMap h' a b h comm (h' x)
  let heT : (h.fiber (h (a x)) : Type u) = h.fiber (b (h' x)) :=
    congrArg (fun Z : Scheme.{u} => (Z : Type u)) (congrArg h.fiber hbase)
  have hm : φ ≫ h.fiberι (b (h' x)) = h'.fiberι (h' x) ≫ a :=
    fiberMap_fiberι h' a b h comm (h' x)
  have hpoint : φ (h'.asFiber x) = cast heT (h.asFiber (a x)) := by
    apply (h.fiberι (b (h' x))).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber,
      fiberι_cast_eq h hbase, Scheme.Hom.fiberι_asFiber]
  have : Etale φ := etale_fiberMap h' a b h comm (h' x)
  calc
    _ = topologicalKrullDimAt (h.fiber (b (h' x))) (cast heT (h.asFiber (a x))) :=
      (fiberDimension_cast_eq h hbase (h.asFiber (a x))).symm
    _ = topologicalKrullDimAt (h.fiber (b (h' x))) (φ (h'.asFiber x)) := by rw [hpoint]
    _ = topologicalKrullDimAt (h'.fiber (h' x)) (h'.asFiber x) :=
      (topologicalKrullDimAt_eq_of_etale φ (h'.asFiber x)).symm

private noncomputable def representativeFiberDimension {X S : GermOfScheme.{u}}
    (r : MorphismOfGerms.Representative X S) : WithBot ℕ∞ :=
  topologicalKrullDimAt (r.hom.fiber (r.hom ⟨X.point, r.mem_source⟩))
    (r.hom.asFiber ⟨X.point, r.mem_source⟩)

private theorem representativeFiberDimension_eq_of_etaleSquare
    {U' U V' V : GermOfScheme.{u}}
    (a : MorphismOfGerms U' U) (b : MorphismOfGerms V' V)
    (h' : MorphismOfGerms U' V') (h : MorphismOfGerms U V)
    (A : MorphismOfGerms.Representative U' U)
    (B : MorphismOfGerms.Representative V' V)
    (H' : MorphismOfGerms.Representative U' V')
    (H : MorphismOfGerms.Representative U V)
    (hAa : MorphismOfGerms.mk A = a) (hBb : MorphismOfGerms.mk B = b)
    (hH'a : MorphismOfGerms.mk H' = h') (hH : MorphismOfGerms.mk H = h)
    (hAet : Etale A.hom) (hBet : Etale B.hom)
    (hsq : MorphismOfGerms.comp h' b =
      MorphismOfGerms.comp a h) :
    representativeFiberDimension H = representativeFiberDimension H' := by
  have hcomp : MorphismOfGerms.mk (MorphismOfGerms.compRepresentative H' B) =
      MorphismOfGerms.mk (MorphismOfGerms.compRepresentative A H) := by
    rw [← hH'a, ← hBb, ← hAa, ← hH] at hsq
    simpa only [MorphismOfGerms.comp_mk] using hsq
  obtain ⟨W, hxW, hWF, hWG, hagree⟩ := MorphismOfGerms.mk_eq_mk_iff.mp hcomp
  let α := MorphismOfGerms.compRepresentative A H
  let β := MorphismOfGerms.compRepresentative H' B
  let q₀ : α.source.toScheme ⟶ H.source.toScheme :=
    (Scheme.Hom.isoImage A.source.ι (A.hom ⁻¹ᵁ H.source)).inv ≫ A.hom ∣_ H.source
  let r₀ : β.source.toScheme ⟶ B.source.toScheme :=
    (Scheme.Hom.isoImage H'.source.ι (H'.hom ⁻¹ᵁ B.source)).inv ≫ H'.hom ∣_ B.source
  let q : W.toScheme ⟶ H.source.toScheme := U'.scheme.homOfLE hWG ≫ q₀
  let r : W.toScheme ⟶ B.source.toScheme := U'.scheme.homOfLE hWF ≫ r₀
  let D : H'.source.toScheme.Opens := H'.hom ⁻¹ᵁ B.source
  let s₀ : β.source.toScheme ⟶ H'.source.toScheme :=
    (Scheme.Hom.isoImage H'.source.ι D).inv ≫ D.ι
  let s : W.toScheme ⟶ H'.source.toScheme := U'.scheme.homOfLE hWF ≫ s₀
  have : Etale q₀ := by
    dsimp [q₀, α, MorphismOfGerms.compRepresentative]
    infer_instance
  have : Etale s₀ := by
    dsimp [s₀, β, D, MorphismOfGerms.compRepresentative]
    infer_instance
  have : Etale q := by dsimp [q]; infer_instance
  have : Etale s := by dsimp [s]; infer_instance
  have hsq₂ : s ≫ H'.hom = r ≫ B.source.ι := by
    simp [s, s₀, r, r₀, D, β,
      MorphismOfGerms.compRepresentative, morphismRestrict_ι, Category.assoc]
  let x' : W.toScheme := ⟨U'.point, hxW⟩
  have hqpoint : q x' = (⟨U.point, H.mem_source⟩ : H.source.toScheme) := by
    change q₀ (U'.scheme.homOfLE hWG ⟨U'.point, hxW⟩) = _
    rw [Scheme.homOfLE_apply' hWG U'.point hxW]
    apply Subtype.ext
    change H.source.ι ((A.hom ∣_ H.source)
      ((A.source.ι.isoImage _).inv ⟨U'.point, _⟩)) = U.point
    rw [← A.map_point, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    change ((A.source.ι.isoImage _).inv ≫ (A.hom ⁻¹ᵁ H.source).ι ≫ A.hom) ⟨U'.point, _⟩ = _
    rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
    change A.hom (U'.scheme.homOfLE _ ⟨U'.point, _⟩) = A.hom ⟨U'.point, A.mem_source⟩
    apply congrArg (fun p : A.source.toScheme ↦ A.hom p)
    apply Subtype.ext
    simp
  have hspoint : s x' = (⟨U'.point, H'.mem_source⟩ : H'.source.toScheme) := by
    change s₀ (U'.scheme.homOfLE hWF ⟨U'.point, hxW⟩) = _
    rw [Scheme.homOfLE_apply' hWF U'.point hxW]
    apply Subtype.ext
    change ((H'.source.ι.isoImage D).inv ≫ D.ι ≫ H'.source.ι) ⟨U'.point, _⟩ = U'.point
    rw [Scheme.Hom.isoImage_inv_ι]
    rfl
  calc
    representativeFiberDimension H =
        topologicalKrullDimAt (H.hom.fiber (H.hom (q x'))) (H.hom.asFiber (q x')) := by
          rw [hqpoint]
          rfl
    _ = topologicalKrullDimAt (r.fiber (r x')) (r.asFiber x') :=
      fiberDimension_eq_of_etaleSquare q B.hom r H.hom hagree.symm x'
    _ = topologicalKrullDimAt (H'.hom.fiber (H'.hom (s x'))) (H'.hom.asFiber (s x')) :=
      (fiberDimension_eq_of_etaleSquare s B.source.ι r H'.hom hsq₂ x').symm
    _ = representativeFiberDimension H' := by
          rw [hspoint]
          rfl

/-- The fibre of a morphism of germs has dimension `d` at its distinguished
point. -/
public abbrev HasFiberDimensionAt (d : ℕ∞)
    {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : MorphismOfGerms.Representative X S,
    MorphismOfGerms.mk g = f ∧
      topologicalKrullDimAt (g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩))
        (g.hom.asFiber ⟨X.point, g.mem_source⟩) = (d : WithBot ℕ∞)

/-- **Stacks Project, Tag 04NL.** Dimension at a point of a fibre is étale
local on the source and target of a morphism of germs. -/
@[stacks 04NL]
public theorem fiberDimensionAt_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    MorphismOfGerms.IsEtaleLocalOnSourceAndTarget (@HasFiberDimensionAt.{u} d) := by
  refine ⟨?_⟩
  rintro U' U V' V a b h' h ⟨A, hAa, hAet⟩ ⟨B, hBb, hBet⟩ hsq
  constructor
  · rintro ⟨H, hH, hHd⟩
    obtain ⟨H', hH'⟩ := MorphismOfGerms.exists_rep h'
    exact ⟨H', hH', (representativeFiberDimension_eq_of_etaleSquare
      a b h' h A B H' H hAa hBb hH' hH hAet hBet hsq).symm.trans hHd⟩
  · rintro ⟨H', hH', hHd⟩
    obtain ⟨H, hH⟩ := MorphismOfGerms.exists_rep h
    exact ⟨H, hH, (representativeFiberDimension_eq_of_etaleSquare
      a b h' h A B H' H hAa hBb hH' hH hAet hBet hsq).trans hHd⟩

end AlgebraicGeometry
