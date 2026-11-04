module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.CompositionAt

/-!
# The cancellation law for étaleness at a point

If a composite `f ≫ q` is étale at `x` and the second factor `q` is étale at `f x`, then the
first factor `f` is étale at `x`. This is the pointwise form of the cancellation law
`AlgebraicGeometry.Etale.of_comp_right` (in
`StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation`).

## Main results

* `AlgebraicGeometry.etaleAt_of_comp_right` is the cancellation law at a single point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The cancellation law for étaleness at a point.** If a composite `f ≫ q` is étale at `x`
and the second factor `q` is étale at `f x`, then the first factor `f` is étale at `x`.

Only the pointwise form is available in the situation this is written for — the last step of the
proof of Stacks 0B0E, where `q` is étale at finitely many chosen points and nowhere else — so
`AlgebraicGeometry.Etale.of_comp_right` cannot be applied directly. The two hypotheses are read
as étaleness of restrictions to open neighbourhoods; the neighbourhood of `x` is cut down to its
part over the neighbourhood of `f x`, exactly as in `AlgebraicGeometry.etaleAt_comp`, which makes
the first factor a morphism between the two restrictions and the global cancellation law
applicable to it. -/
theorem etaleAt_of_comp_right {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) {x : X}
    (hcomp : EtaleAt (f ≫ q) x) (hq : EtaleAt q (f.base x)) : EtaleAt f x := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open (f ≫ q) x).mp hcomp
  obtain ⟨W, hfxW, hW⟩ := (etaleAt_iff_exists_open q (f.base x)).mp hq
  have := hU
  have := hW
  set A : U.toScheme.Opens := (U.ι ≫ f) ⁻¹ᵁ W with hAdef
  have hxA : (⟨x, hxU⟩ : U.toScheme) ∈ A := hfxW
  have hres : (U.ι ≫ f).resLE W A le_rfl ≫ W.ι = A.ι ≫ U.ι ≫ f :=
    Scheme.Hom.resLE_comp_ι (U.ι ≫ f) (le_rfl : A ≤ (U.ι ≫ f) ⁻¹ᵁ W)
  have heq : (U.ι ≫ f).resLE W A le_rfl ≫ W.ι ≫ q = A.ι ≫ U.ι ≫ (f ≫ q) := by
    rw [← Category.assoc, hres]
    simp only [Category.assoc]
  have : Etale ((U.ι ≫ f).resLE W A le_rfl ≫ W.ι ≫ q) := by
    rw [heq]
    infer_instance
  have : Etale ((U.ι ≫ f).resLE W A le_rfl) := Etale.of_comp_right _ (W.ι ≫ q)
  have : Etale ((A.ι ≫ U.ι) ≫ f) := by
    rw [Category.assoc, ← hres]
    infer_instance
  have hpt : EtaleAt ((A.ι ≫ U.ι) ≫ f) (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) :=
    (etale_iff_forall_etaleAt _).mp inferInstance _
  have hbase : (A.ι ≫ U.ι).base (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) = x := rfl
  have h := etaleAt_of_open_precomp (A.ι ≫ U.ι) f (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) hpt
  rwa [hbase] at h

end AlgebraicGeometry
