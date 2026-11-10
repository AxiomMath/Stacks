module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Flat pullback of cycles on varieties

Chapter 43 of the Stacks Project specialises the Chow homology of chapter 42 to varieties over a
field `k`, that is to the base situation `Spec k` with the zero dimension function
(`Stacks.Chow.fieldChowSituation`), where the delta-dimension of an integral closed subscheme is
its dimension. For a flat morphism `f : X ⟶ Y` of varieties over `k` the fibres all have
dimension `r = dim X - dim Y`, so `f` has relative dimension `r` in the sense of Stacks 02NJ and
flat pullback raises degrees by `r`. Stacks 0AZF is then the cycle identity of Stacks 02RE read
in this situation:

`f^*[F]_k = [f^*F]_{k+r}` for `F` coherent on `Y` with `dim Supp(F) ≤ k`.

Stacks 0B0P is the functoriality of Stacks 02RD read in the same situation: for flat morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z` of varieties over `k` the composite is flat and

`f^* ∘ g^* = (g ∘ f)^*`   as maps `Z_j(Z) ⟶ Z_{j + dim X - dim Z}(X)`,

the degree shift being `(dim X - dim Y) + (dim Y - dim Z)`.

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isVariety` — the dimension of a
  variety is a natural number.
* `AlgebraicGeometry.locallyOfFiniteType_of_isVariety_comp` — a morphism of varieties over `k` is
  locally of finite type.
* `AlgebraicGeometry.relativeDimension_of_flat_of_isVariety` — a flat morphism of varieties has
  relative dimension `dim X - dim Y`, the fibre-dimension formula of Stacks 02JS which the source
  invokes in the introduction to the section.
* `Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le` — over a field
  the delta-dimension of the support of a coherent sheaf is bounded by its topological dimension,
  which is what makes the hypothesis of the lemma below the hypothesis of the source.
* `Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety` — **Stacks 0AZF**.
* `Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety'` — the same, with the
  dimension of the support written topologically.
* `AlgebraicGeometry.relativeDimension_comp_of_flat_of_isVariety` — a composite of flat morphisms
  of varieties has relative dimension `dim X - dim Z`.
* `Stacks.Chow.flatPullback_comp_apply_of_isVariety` — the pullback identity coefficientwise.
* `Stacks.Chow.flatPullback_comp_of_isVariety` — the pullback identity.
* `Stacks.Chow.flat_comp_and_flatPullback_comp_of_isVariety` — **Stacks 0B0P**, both clauses:
  the composite is flat and `f^* ∘ g^* = (g ∘ f)^*`.

## Implementation notes

`r = dim X - dim Y` is spelled as a natural number `r` together with the hypothesis
`dim X = dim Y + r`; no extended-integer subtraction and no truncated natural subtraction occurs.
The dimensions themselves are `WithBot ℕ∞`-valued, as `TopologicalSpace.topologicalKrullDim` is,
and the equality says exactly that `r` is the difference. The degree `k + r` of the conclusion is
ordinary addition in `ℤ`, the degree type of `Stacks.Chow.CycleGroup`; the extended integers
`EInt` occur only in the dimension hypothesis on the support, where they are needed because the
delta-dimension of a possibly empty scheme is `⊥`.

The hypothesis "the dimension of the support of `F` is at most `k`" is stated as the
delta-dimension bound `Stacks.Chow.schemeDeltaDimension ... ≤ k`, which over `Spec k` *is* the
dimension of the support and is the form the cycle `[F]_k` is formed from. The primed version
below states it as `topologicalKrullDim (Supp F) ≤ n` for a natural number `n`, the two being
related by `Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le`.

That `f` is locally of finite type is not assumed: it follows from the two variety structures and
from `f` being a morphism over `k`, and is installed in the statement by
`AlgebraicGeometry.locallyOfFiniteType_of_isVariety_comp`. Likewise the relative dimension of `f`
and the coherence of `f^*F` are supplied, not assumed.

The relative dimension is computed from Stacks 02JS. Since `Spec k` has one point, the fibre of
the structure morphism of a variety through a point is the variety itself, so the local dimension
of the fibre at that point is the local dimension of the variety, which by Stacks 0A21 is the
dimension of the variety because a variety is irreducible. Flatness turns the inequality of
Stacks 02JS for the composition `X ⟶ Y ⟶ Spec k` into an equality, which reads
`dim X = dim_x(f^{-1}(f x)) + dim Y`; cancelling the finite `dim Y` leaves `r`. Constancy of the
local dimension of the fibres then gives both halves of `AlgebraicGeometry.RelativeDimension`.

The degree shift of the composite is the natural number `r + s`, whereas pulling back first along
`g` and then along `f` lands in degree `(j + s) + r`; the two are equal and the final statement of
Stacks 0B0P transports along that equality, exactly as `Stacks.Chow.flatPullback_comp` does. The
coefficientwise form needs no transport, both sides being integers.

## References

* [Stacks Project, Tag 0AZF](https://stacks.math.columbia.edu/tag/0AZF)
* [Stacks Project, Tag 0B0P](https://stacks.math.columbia.edu/tag/0B0P)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 020D](https://stacks.math.columbia.edu/tag/020D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The dimension of a variety -/

/-- **The dimension of a variety is a natural number.** It is not `⊥` because a variety is
nonempty, being integral, and not `⊤` because a scheme quasi-compact and locally of finite type
over a field has finite dimension. -/
theorem exists_topologicalKrullDim_eq_natCast_of_isVariety (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsVariety k sX] :
    ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hne : topologicalKrullDim X ≠ ⊤ :=
    topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have hnn : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    have : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    Order.krullDim_nonneg
  have hbot : topologicalKrullDim X ≠ ⊥ := fun hb => by simp [hb] at hnn
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hytop : y ≠ ⊤ := by
    intro ht
    apply hne
    rw [← hy, ht]
    rfl
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hytop
  refine ⟨n, ?_⟩
  rw [← hy, ← hn]
  rfl

/-- A morphism of varieties over `k` is locally of finite type: it is so after composing with the
structure morphism of its target, which is the structure morphism of its source. -/
theorem locallyOfFiniteType_of_isVariety_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) : LocallyOfFiniteType f := by
  have : LocallyOfFiniteType (f ≫ sY) := by
    rw [hbase]
    infer_instance
  exact locallyOfFiniteType_of_comp f sY

/-! ### The relative dimension of a flat morphism of varieties -/

/-- Over a one-point base the fibre of a morphism through a point is the whole source, so the
local dimension of the fibre there is the local dimension of the source. -/
private theorem fiber_topologicalKrullDimAt_eq {X S : Scheme.{u}} (p : X ⟶ S) [Subsingleton S]
    (x : X) :
    topologicalKrullDimAt (p.fiber (p.base x)) (p.asFiber x) = topologicalKrullDimAt X x := by
  have hpre : p.base ⁻¹' ({p.base x} : Set S) = Set.univ := by
    ext y
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim (p.base y) (p.base x)⟩
  let e : p.fiber (p.base x) ≃ₜ X :=
    (p.fiberHomeo (p.base x)).trans
      ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  have he : e (p.asFiber x) = x := by
    change ((p.fiberHomeo (p.base x)) (p.asFiber x)).1 = x
    exact p.fiberι_asFiber x
  exact (topologicalKrullDimAt_eq_of_homeomorph e (p.asFiber x)).trans (congrArg _ he)

/-- A point of the fibre of `f` over `s` is `f.asFiber` of its image, transported along the
equality of base points. -/
private theorem asFiber_fiberι {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : f.fiber s)
    (h : f.base (f.fiberι s z) = s) : h ▸ f.asFiber (f.fiberι s z) = z := by
  apply (f.fiberHomeo s).injective
  apply Subtype.ext
  simp only [Scheme.Hom.fiberHomeo_apply]
  have htr : ∀ {s' : S} (hs : s' = s) (w : f.fiber s'),
      f.fiberι s (hs ▸ w) = f.fiberι s' w := by
    rintro s' rfl w
    rfl
  rw [htr h, Scheme.Hom.fiberι_asFiber]

/-- Transport of the local dimension of a fibre along an equality of base points. -/
private theorem fiber_topologicalKrullDimAt_transport {X S : Scheme.{u}} (f : X ⟶ S) {s t : S}
    (h : s = t) (z : f.fiber s) :
    topologicalKrullDimAt (f.fiber t) (h ▸ z) = topologicalKrullDimAt (f.fiber s) z := by
  subst h
  rfl

/-- Solving for an unknown summand in `WithBot ℕ∞` when the other summand and the total are
natural numbers: neither `⊥` nor `⊤` can occur, so the equation is one of natural numbers. -/
private theorem withBot_enat_eq_natCast_sub {x : WithBot ℕ∞} {m n : ℕ}
    (h : x + (n : WithBot ℕ∞) = (m : WithBot ℕ∞)) :
    x = ((m - n : ℕ) : WithBot ℕ∞) := by
  cases x with
  | bot => simp at h
  | coe y =>
    cases y with
    | top =>
      have h' : (⊤ : ℕ∞) + (n : ℕ∞) = (m : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe a =>
      have h' : a + n = m := by exact_mod_cast h
      rw [show a = m - n by omega]
      norm_cast

/-- **The fibre-dimension formula for a flat morphism of varieties, Stacks 02JS.** A flat
morphism `f : X ⟶ Y` of varieties over `k` with `dim X = dim Y + r` has relative dimension `r`:
every nonempty fibre is equidimensional of dimension `r`. -/
theorem relativeDimension_of_flat_of_isVariety (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hbase
    RelativeDimension f r := by
  let _ : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hbase
  have : Subsingleton (Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k)
    exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField k)
  obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k sX
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k sY
  have hdiff : dX - dY = r := by
    rw [hdX, hdY] at hr
    have : dX = dY + r := by exact_mod_cast hr
    omega
  have hpoint : ∀ x : X,
      topologicalKrullDimAt (f.fiber (f.base x)) (f.asFiber x) = (r : WithBot ℕ∞) := by
    intro x
    have hcomp := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt f sY x (Flat.stalkMap f x)
    rw [fiber_topologicalKrullDimAt_eq (f ≫ sY) x,
      fiber_topologicalKrullDimAt_eq sY (f.base x),
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y sY (f.base x),
      hdX, hdY] at hcomp
    rw [withBot_enat_eq_natCast_sub hcomp.symm, hdiff]
  intro s hs
  have := hs
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f (Y.fromSpecResidueField s))
    infer_instance
  have hall : ∀ z : f.fiber s, topologicalKrullDimAt (f.fiber s) z = (r : WithBot ℕ∞) := by
    intro z
    have hx : f.base (f.fiberι s z) = s := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.fiberHomeo_apply]
        using (f.fiberHomeo s z).property
    calc
      topologicalKrullDimAt (f.fiber s) z =
          topologicalKrullDimAt (f.fiber s) (hx ▸ f.asFiber (f.fiberι s z)) := by
        rw [asFiber_fiberι f s z hx]
      _ = topologicalKrullDimAt (f.fiber (f.base (f.fiberι s z)))
            (f.asFiber (f.fiberι s z)) :=
        fiber_topologicalKrullDimAt_transport f hx (f.asFiber (f.fiberι s z))
      _ = (r : WithBot ℕ∞) := hpoint (f.fiberι s z)
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (Y.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hall, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hlocal (z : f.fiber s) : localKrullDim (f.fiber s) z = (r : WithBot ℕ∞) := by
    rw [← topologicalKrullDimAt_eq_localKrullDim, hall]
  simp [hlocal]

/-- **The relative dimension of a composite of flat morphisms of varieties.** If `f : X ⟶ Y` and
`g : Y ⟶ Z` are flat morphisms of varieties over `k` with `dim X = dim Y + r` and
`dim Y = dim Z + s`, then `f ≫ g` has relative dimension `r + s = dim X - dim Z`. -/
theorem relativeDimension_comp_of_flat_of_isVariety (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY] [IsVariety k sZ]
    (f : X ⟶ Y) [Flat f] (g : Y ⟶ Z) [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (hs : topologicalKrullDim Y = topologicalKrullDim Z + (s : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType (f ≫ g) :=
      locallyOfFiniteType_of_isVariety_comp k sX sZ (f ≫ g)
        (by rw [Category.assoc, hgbase, hfbase])
    RelativeDimension (f ≫ g) (r + s) := by
  have hrs : topologicalKrullDim X = topologicalKrullDim Z + ((r + s : ℕ) : WithBot ℕ∞) := by
    rw [hr, hs, Nat.cast_add, add_assoc, add_comm (s : WithBot ℕ∞)]
  exact relativeDimension_of_flat_of_isVariety k sX sZ (f ≫ g)
    (by rw [Category.assoc, hgbase, hfbase]) (r + s) hrs

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The dimension of the support over a field -/

/-- **Over a field the delta-dimension of the support of a coherent sheaf is its dimension.** If
the support of a coherent sheaf on a scheme locally of finite type over `k` has topological
dimension at most `n`, then its delta-dimension for the base situation `Spec k` is at most `n`. -/
theorem schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le (k : Type u) [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
    (F : Y.Modules) [F.IsCoherent] (n : ℕ)
    (hFn : topologicalKrullDim (SheafOfModules.supp F) ≤ (n : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation k) ((reducedSupport F).subschemeι ≫ sY) ≤
      (((n : ℤ)) : EInt) := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  exact schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) sY F fun x hx =>
    relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
      (fun _ _ => rfl) sY (SheafOfModules.isClosed_supp F) hFn hx

/-! ### Stacks 0AZF -/

/-- **Stacks 0AZF.** Let `f : X ⟶ Y` be a flat morphism of varieties over a field `k` and set
`r = dim X - dim Y`. If `F` is a coherent sheaf on `Y` whose support has dimension at most `k`,
then

`f^*[F]_k = [f^*F]_{k+r}`.

The dimension of the support is read as the delta-dimension of the base situation `Spec k`, which
over a field is the dimension; see
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety'` for the topological
form. -/
@[stacks 0AZF]
theorem flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (F : Y.Modules) [hF : F.IsCoherent] (j : ℤ)
    (hFj : schemeDeltaDimension (fieldChowSituation k)
      ((reducedSupport F).subschemeι ≫ sY) ≤ (j : EInt)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hbase
    flatPullback (fieldChowSituation k) sX sY f hbase r
        (relativeDimension_of_flat_of_isVariety k sX sY f hbase r hr) j
        (cycleAssociatedToCoherentSheaf (fieldChowSituation k) sY F j hFj) =
      @cycleAssociatedToCoherentSheaf X (fieldChowSituation k) sX inferInstance
        ((Scheme.Modules.pullback f).obj F)
        (@AlgebraicGeometry.isCoherent_pullback X Y
          (LocallyOfFiniteType.isLocallyNoetherian sX) f F hF)
        (j + (r : ℤ))
        (schemeDeltaDimension_support_pullback_le (fieldChowSituation k) sX sY f hbase r
          (relativeDimension_of_flat_of_isVariety k sX sY f hbase r hr) F j hFj) := by
  let _ : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hbase
  exact flatPullback_cycleAssociatedToCoherentSheaf (fieldChowSituation k) sX sY f hbase r
    (relativeDimension_of_flat_of_isVariety k sX sY f hbase r hr) F j hFj

/-- **Stacks 0AZF, with the dimension of the support written topologically.** -/
theorem flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety' (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (F : Y.Modules) [hF : F.IsCoherent] (n : ℕ)
    (hFn : topologicalKrullDim (SheafOfModules.supp F) ≤ (n : WithBot ℕ∞)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hbase
    flatPullback (fieldChowSituation k) sX sY f hbase r
        (relativeDimension_of_flat_of_isVariety k sX sY f hbase r hr) (n : ℤ)
        (cycleAssociatedToCoherentSheaf (fieldChowSituation k) sY F (n : ℤ)
          (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sY F n hFn)) =
      @cycleAssociatedToCoherentSheaf X (fieldChowSituation k) sX inferInstance
        ((Scheme.Modules.pullback f).obj F)
        (@AlgebraicGeometry.isCoherent_pullback X Y
          (LocallyOfFiniteType.isLocallyNoetherian sX) f F hF)
        ((n : ℤ) + (r : ℤ))
        (schemeDeltaDimension_support_pullback_le (fieldChowSituation k) sX sY f hbase r
          (relativeDimension_of_flat_of_isVariety k sX sY f hbase r hr) F (n : ℤ)
          (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sY F n hFn)) :=
  flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety k sX sY f hbase r hr F (n : ℤ)
    (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sY F n hFn)

/-! ### Stacks 0B0P -/

/-- **Stacks 0B0P, coefficientwise.** Flat pullback of cycles on varieties over `k` is compatible
with composition, read off at a single point of `X`. The degrees are `j + s` after `g` and
`(j + s) + r` after `f`, with `r = dim X - dim Y` and `s = dim Y - dim Z`. -/
theorem flatPullback_comp_apply_of_isVariety (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] [IsVariety k sZ]
    (f : X ⟶ Y) [Flat f] (g : Y ⟶ Z) [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (hs : topologicalKrullDim Y = topologicalKrullDim Z + (s : WithBot ℕ∞))
    (j : ℤ) (c : CycleGroup (fieldChowSituation k) sZ j) (x : X) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
    letI : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
    (flatPullback (fieldChowSituation k) sX sY f hfbase r
          (relativeDimension_of_flat_of_isVariety k sX sY f hfbase r hr) (j + (s : ℤ))
          (flatPullback (fieldChowSituation k) sY sZ g hgbase s
            (relativeDimension_of_flat_of_isVariety k sY sZ g hgbase s hs) j c)).1 x =
      (flatPullback (fieldChowSituation k) sX sZ (f ≫ g)
        (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (relativeDimension_comp_of_flat_of_isVariety k sX sY sZ f g hfbase hgbase r s hr hs)
        j c).1 x := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
  exact flatPullback_comp_apply (fieldChowSituation k) sX sY sZ f g hfbase hgbase r s
    (relativeDimension_of_flat_of_isVariety k sX sY f hfbase r hr)
    (relativeDimension_of_flat_of_isVariety k sY sZ g hgbase s hs) j c x

/-- **Stacks 0B0P, the pullback identity.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be flat morphisms of
varieties over a field `k`. Then `f^* ∘ g^* = (g ∘ f)^*` as maps
`Z_j(Z) ⟶ Z_{j + dim X - dim Z}(X)`.

This is the pullback identity of Tag 0B0P on its own. The relative dimension `dim X - dim Z` of
the composite, which fixes the degree of the right-hand side, is
`AlgebraicGeometry.relativeDimension_comp_of_flat_of_isVariety`. The tag is registered on the
statement of both of its clauses, this identity together with the flatness of the composite, in
`Stacks.Chow.flat_comp_and_flatPullback_comp_of_isVariety`. -/
theorem flatPullback_comp_of_isVariety (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] [IsVariety k sZ]
    (f : X ⟶ Y) [Flat f] (g : Y ⟶ Z) [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (hs : topologicalKrullDim Y = topologicalKrullDim Z + (s : WithBot ℕ∞))
    (j : ℤ) (hcast : j + (s : ℤ) + (r : ℤ) = j + ((r + s : ℕ) : ℤ))
    (c : CycleGroup (fieldChowSituation k) sZ j) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
    letI : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
    (hcast ▸ flatPullback (fieldChowSituation k) sX sY f hfbase r
          (relativeDimension_of_flat_of_isVariety k sX sY f hfbase r hr) (j + (s : ℤ))
          (flatPullback (fieldChowSituation k) sY sZ g hgbase s
            (relativeDimension_of_flat_of_isVariety k sY sZ g hgbase s hs) j c) :
        CycleGroup (fieldChowSituation k) sX (j + ((r + s : ℕ) : ℤ))) =
      flatPullback (fieldChowSituation k) sX sZ (f ≫ g)
        (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (relativeDimension_comp_of_flat_of_isVariety k sX sY sZ f g hfbase hgbase r s hr hs)
        j c := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
  exact flatPullback_comp (fieldChowSituation k) sX sY sZ f g hfbase hgbase r s
    (relativeDimension_of_flat_of_isVariety k sX sY f hfbase r hr)
    (relativeDimension_of_flat_of_isVariety k sY sZ g hgbase s hs) j hcast c

/-! ### The whole of Stacks 0B0P -/

/-- **Stacks Project, Tag 0B0P.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be flat morphisms of varieties
over a field `k`. Then `g ∘ f` is flat and

`f^* ∘ g^* = (g ∘ f)^*`   as maps `Z_j(Z) ⟶ Z_{j + dim X - dim Z}(X)`.

`WithBot ℕ∞` has no subtraction, so `r = dim X - dim Y` and `s = dim Y - dim Z` are natural
numbers together with the relations `dim X = dim Y + r` and `dim Y = dim Z + s`, and the degree
`dim X - dim Z` of the composite is `r + s`. Pulling back first along `g` and then along `f`
lands in degree `(j + s) + r`, so the left-hand side is transported along the equality `hcast`
of that degree with `j + (r + s)`, exactly as `Stacks.Chow.flatPullback_comp` does. -/
@[stacks 0B0P "the whole lemma: both that the composite of two flat morphisms of varieties over \
a field is flat and the identity `f^* ∘ g^* = (g ∘ f)^*` of flat pullbacks of cycles, as maps \
`Z_j(Z) ⟶ Z_{j + dim X - dim Z}(X)`, under the source's own hypotheses that `f : X ⟶ Y` and \
`g : Y ⟶ Z` are flat morphisms of varieties over `k`. Flat pullback is the homomorphism \
`Stacks.Chow.flatPullback` of Tag 02RB in the base situation `Spec k` with the zero dimension \
function, where the delta-dimension of an integral closed subscheme is its dimension, so the \
cycle groups are the source's `Z_j`. `WithBot ℕ∞` has no subtraction, so the relative \
dimensions `r = dim X - dim Y` and `s = dim Y - dim Z` are natural numbers together with the \
relations `dim X = dim Y + r` and `dim Y = dim Z + s`, and the source's degree shift \
`dim X - dim Z` is `r + s`; `hcast` is the equality in `ℤ` of the degree `(j + s) + r` reached \
by pulling back along `g` and then `f` with the degree `j + (r + s)` of the right-hand side, \
along which the left-hand side is transported. That the relative dimension of the composite is \
`r + s` is `AlgebraicGeometry.relativeDimension_comp_of_flat_of_isVariety`, the fibre-dimension \
formula of Tag 02JS which the section's introduction invokes, and the coefficientwise form of \
the identity is `Stacks.Chow.flatPullback_comp_apply_of_isVariety`."]
theorem flat_comp_and_flatPullback_comp_of_isVariety (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] [IsVariety k sZ]
    (f : X ⟶ Y) [Flat f] (g : Y ⟶ Z) [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ)
    (hr : topologicalKrullDim X = topologicalKrullDim Y + (r : WithBot ℕ∞))
    (hs : topologicalKrullDim Y = topologicalKrullDim Z + (s : WithBot ℕ∞))
    (j : ℤ) (hcast : j + (s : ℤ) + (r : ℤ) = j + ((r + s : ℕ) : ℤ))
    (c : CycleGroup (fieldChowSituation k) sZ j) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
    letI : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
    Flat (f ≫ g) ∧
      (hcast ▸ flatPullback (fieldChowSituation k) sX sY f hfbase r
            (relativeDimension_of_flat_of_isVariety k sX sY f hfbase r hr) (j + (s : ℤ))
            (flatPullback (fieldChowSituation k) sY sZ g hgbase s
              (relativeDimension_of_flat_of_isVariety k sY sZ g hgbase s hs) j c) :
          CycleGroup (fieldChowSituation k) sX (j + ((r + s : ℕ) : ℤ))) =
        flatPullback (fieldChowSituation k) sX sZ (f ≫ g)
          (by rw [Category.assoc, hgbase, hfbase]) (r + s)
          (relativeDimension_comp_of_flat_of_isVariety k sX sY sZ f g hfbase hgbase r s hr hs)
          j c := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp k sX sY f hfbase
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_isVariety_comp k sY sZ g hgbase
  exact ⟨inferInstance,
    flatPullback_comp_of_isVariety k sX sY sZ f g hfbase hgbase r s hr hs j hcast c⟩

end Stacks.Chow

end
