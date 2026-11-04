module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeFrobeniusDegree
public import StacksFrontier.FieldTheory.SeparableCompositumFrobenius
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The function field of a smooth curve and the compositum of the `p`-th powers

Let `k` be a field of characteristic `p` and let `X` be a smooth curve over `k`. This file
collects the facts about the function field `K = k(X)` that are needed to compare `K` with the
compositum `kKᵖ` of the image of `k` with the `p`-th powers of `K`, the subfield
`compositumFrobenius k K p`.

The function field has characteristic `p` because it is an extension of `k`. Smoothness makes `X`
geometrically reduced, which by Tag 04KS is separability of `K/k` in the sense of Tag 030O; and
separability is formal smoothness of `K/k` by Tag 0321. A curve is exactly a variety whose
function field has transcendence degree one over `k`, so the degree `[K : kKᵖ] = p ^ trdeg(K/k)`
of Tag 07P2 is `p` itself; this is the one-dimensional case of the degree computation behind Tag
0CCF.

A `k`-algebra equivalence of fields carries `kKᵖ` onto `kKᵖ`, because it preserves both
generating sets: the image of `k` and the `p`-th powers.

When `X` is in addition proper over `k`, its ring of global functions is a finite `k`-algebra, so
every global function is integral over `k`; separability of `K/k` then puts the germ of every
global function at the generic point inside `kKᵖ`.

## Main results

* `map_compositumFrobenius` — a `k`-algebra equivalence of fields carries the compositum of the
  base with the `p`-th powers onto the compositum.
* `AlgebraicGeometry.charP_functionField` — the function field of an integral scheme over `k` has
  the characteristic of `k`.
* `AlgebraicGeometry.isSeparableExtension_functionField_of_smooth` — the function field of a
  smooth variety is a separable extension of the base field.
* `AlgebraicGeometry.finrank_compositumFrobenius_functionField` — the function field of a smooth
  curve has degree `p` over the compositum of the base field with its `p`-th powers.
* `AlgebraicGeometry.germToFunctionField_mem_compositumFrobenius` — on a smooth proper variety the
  germ at the generic point of a global function lies in that compositum.

## Implementation notes

The `k`-algebra structure on `X.functionField` used throughout is
`AlgebraicGeometry.varietyFunctionFieldAlgebra`, the one built from the stalk map of the
structure morphism at the generic point; it is carried in the statements by a `letI`, since a
scheme together with a structure morphism to `Spec k` is not literally the bundled
`AlgebraicGeometry.Variety` that the instance is stated for. Tag 04KS is available for the
equivalent description of that algebra through global sections, and
`AlgebraicGeometry.varietyFunctionFieldAlgebra_eq_germToFunctionField` identifies the two.

Characteristic of the function field needs only an integral scheme over `k`, separability needs
only a smooth variety, and membership of the germs of global functions needs a smooth proper
variety, so none of the three is restricted to curves. The degree over the compositum is the only
statement that uses dimension one, through
`AlgebraicGeometry.isCurve_iff_trdeg_functionField_eq_one`.

For a dominant morphism of curves over `k` the induced extension of function fields is finite;
that is `AlgebraicGeometry.finiteDimensional_functionField_of_isCurve`.

## References

* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
* [Stacks Project, Tag 0321](https://stacks.math.columbia.edu/tag/0321)
* [Stacks Project, Tag 07P2](https://stacks.math.columbia.edu/tag/07P2)
* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- A `k`-algebra equivalence of fields carries the compositum `kKᵖ` of the base field with the
`p`-th powers onto the compositum `kK'ᵖ`: it is a ring isomorphism commuting with the structure
map, so it matches the two generating sets. -/
theorem map_compositumFrobenius {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] (p : ℕ) (e : K ≃ₐ[k] K') :
    Subfield.map (e : K →+* K') (compositumFrobenius k K p) = compositumFrobenius k K' p := by
  refine le_antisymm (Subfield.map_le_iff_le_comap.mpr (Subfield.closure_le.mpr ?_))
    (Subfield.closure_le.mpr ?_)
  · rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, by simp⟩)
    · exact Subfield.subset_closure (Or.inr ⟨e b, by simp⟩)
  · rintro y (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact Subfield.mem_map.mpr
        ⟨algebraMap k K a, Subfield.subset_closure (Or.inl ⟨a, rfl⟩), by simp⟩
    · exact Subfield.mem_map.mpr
        ⟨e.symm b ^ p, Subfield.subset_closure (Or.inr ⟨e.symm b, rfl⟩), by simp⟩

/-- Membership in the compositum `kKᵖ` of the base field with the `p`-th powers is invariant
under a `k`-algebra equivalence of fields. -/
theorem mem_compositumFrobenius_algEquiv_iff {k K K' : Type*} [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] (p : ℕ) (e : K ≃ₐ[k] K') (x : K) :
    e x ∈ compositumFrobenius k K' p ↔ x ∈ compositumFrobenius k K p := by
  rw [← map_compositumFrobenius p e]
  exact Subfield.map_mem_map (e : K →+* K')

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The top open of an integral scheme is nonempty, witnessed by the generic point. -/
private instance nonempty_top_opens {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The function field of an integral scheme over a field of characteristic `p` has
characteristic `p`: the global sections of the structure morphism followed by the germ at the
generic point make it an extension field of the base. -/
theorem charP_functionField (p : ℕ) [CharP k p] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsIntegral X] : CharP X.functionField p := by
  let ι : k →+* X.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.germToFunctionField ⊤).hom
  exact (ι.charP_iff_charP p).mp inferInstance

/-- **Separability of the function field of a smooth variety, Tag 030O for `k(X)/k`.** A smooth
variety over `k` is geometrically reduced, and by Tag 04KS geometric reducedness of an integral
scheme over a field is separability of its function field over that field. -/
theorem isSeparableExtension_functionField_of_smooth {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsVariety k pX] [Smooth pX] :
    letI : Algebra k X.functionField :=
      varietyFunctionFieldAlgebra ({ toScheme := X, structureMap := pX } : Variety k)
    Algebra.IsSeparableExtension k X.functionField := by
  let VX : Variety k := { toScheme := X, structureMap := pX }
  show @Algebra.IsSeparableExtension k X.functionField _ _ (varietyFunctionFieldAlgebra VX)
  rw [varietyFunctionFieldAlgebra_eq_germToFunctionField VX]
  exact (geometricallyReduced_iff_isSeparableExtension_functionField pX).mp
    (geometricallyReduced_of_smooth pX)

/-- **The one-dimensional case of the degree of Tag 07P2.** The function field of a smooth curve
over a field `k` of characteristic `p` has degree `p` over the compositum of `k` with its `p`-th
powers: the extension is formally smooth because it is separable, so its degree over the
compositum is `p` raised to the transcendence degree, which is one for a curve. -/
theorem finrank_compositumFrobenius_functionField (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] :
    letI : Algebra k X.functionField :=
      varietyFunctionFieldAlgebra ({ toScheme := X, structureMap := pX } : Variety k)
    Module.finrank (compositumFrobenius k X.functionField p) X.functionField = p := by
  let VX : Variety k := { toScheme := X, structureMap := pX }
  let : Algebra k X.functionField := varietyFunctionFieldAlgebra VX
  have : CharP X.functionField p := charP_functionField p pX
  have : Algebra.EssFiniteType k X.functionField := varietyFunctionField_essFiniteType VX
  have : Algebra.FormallySmooth k X.functionField :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k X.functionField).mpr
      (isSeparableExtension_functionField_of_smooth pX)
  have htr : Algebra.trdeg k X.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VX).mp inferInstance
  show Module.finrank (compositumFrobenius k X.functionField p) X.functionField = p
  rw [finrank_compositumFrobenius_eq_pow_trdeg p, Cardinal.toNat_eq_one.mpr htr, pow_one]

/-- **A global function on a smooth proper variety lies in the compositum of the base field with
the `p`-th powers of the function field.** Properness makes the ring of global functions a finite
`k`-algebra, so every global function is integral over `k`, and so is its germ at the generic
point; an element of a separable extension that is integral over the base lies in the
compositum. -/
theorem germToFunctionField_mem_compositumFrobenius (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsVariety k pX] [Smooth pX] [IsProper pX] :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    letI : Algebra k X.functionField :=
      varietyFunctionFieldAlgebra ({ toScheme := X, structureMap := pX } : Variety k)
    ∀ a : Γ(X, ⊤),
      (X.germToFunctionField ⊤).hom a ∈ compositumFrobenius k X.functionField p := by
  let VX : Variety k := { toScheme := X, structureMap := pX }
  let : Algebra k X.functionField := varietyFunctionFieldAlgebra VX
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop).hom.toAlgebra
  have hmap : algebraMap k X.functionField =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.germToFunctionField ⊤).hom :=
    functionFieldAlgebraMap_eq_germToFunctionField VX
  have : IsScalarTower k Γ(X, ⊤) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (by rw [hmap]; rfl)
  have : CharP X.functionField p := charP_functionField p pX
  have : Algebra.IsSeparableExtension k X.functionField :=
    isSeparableExtension_functionField_of_smooth pX
  have : Module.Finite k Γ(X, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k pX).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))
  exact fun a => mem_compositumFrobenius_of_isIntegral p _
    ((Algebra.IsIntegral.of_finite k Γ(X, ⊤)).isIntegral a).algebraMap

end AlgebraicGeometry

end
