module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberLocalRingDimension
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# The local ring of a fibre after base change

Let `f : X ⟶ S` be locally of finite type and let

```
X' ---g'---> X
|            |
f'           f
v            v
S' ---g----> S
```

be a fibre product diagram. Fix `x' : X'` and write `x = g' x'`, `s' = f' x'` and
`s = g s' = f x`. The morphism of fibres `X'_{s'} ⟶ X_s` induced by the square is
`AlgebraicGeometry.fiberMap`; let `F` be its fibre over `x`. The dimension of the local ring of
`F` at `x'` measures exactly the dimension gained by the base change: it is the difference
`dim O_{X'_{s'}, x'} - dim O_{X_s, x}` and also the difference
`trdeg_{κ(s)} κ(x) - trdeg_{κ(s')} κ(x')`. In particular the local dimension of the fibre cannot
drop and the residue-field transcendence degree cannot grow. Moreover, with `s'`, `s` and `x`
given, the point `x'` above them can be chosen so that neither invariant changes.

Both differences are stated additively, Krull dimensions of rings taking values in `WithBot ℕ∞`
and transcendence degrees being compared through `Cardinal.toENat`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` is the
  scheme-theoretic dimension formula for a flat morphism (Stacks Tag 00ON): the local dimension
  of the source is the local dimension of the target plus the local dimension of the fibre.
* `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq` and
  `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_trdeg_eq` are the two equalities of
  **Stacks Tag 02FY part (2)**.
* `AlgebraicGeometry.ringKrullDim_stalk_fiber_le_of_baseChange` and
  `AlgebraicGeometry.trdeg_residueField_le_of_baseChange` are the two inequalities they imply.

## Implementation notes

The induced morphism of fibres is the pullback square of residue fields supplied by
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, so it is flat, being a base
change of the field extension `κ(s) ⟶ κ(s')`. Both fibres are locally Noetherian because `f` is
locally of finite type over a field, so the dimension formula for a flat local homomorphism of
Noetherian local rings applies to the stalk map, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk` identifies its closed fibre with the local ring
of the fibre. The passage to transcendence degrees uses the invariance of the *topological*
dimension of the fibre, which is part (1) of the same tag, together with the dimension formula
for a fibre at a point (Stacks Tag 02FX).

Points of successive fibres are named canonically by `AlgebraicGeometry.Scheme.Hom.asFiber`, so
no choice of a point of a fibre product is made.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Reading the local dimension of a fibre at a point of the ambient scheme, through the
homeomorphism onto the topological fibre, agrees with reading it at the canonical point of the
fibre through that point. -/
lemma ringKrullDim_stalk_fiberHomeo_symm {A B : Scheme.{u}} (q : A ⟶ B) (a : A) (b : B)
    (hb : q a = b) :
    ringKrullDim ((q.fiber b).presheaf.stalk ((q.fiberHomeo b).symm ⟨a, hb⟩)) =
      ringKrullDim ((q.fiber (q a)).presheaf.stalk (q.asFiber a)) := by
  subst b
  rfl

/-- Reading the local dimension of a fibre is compatible with replacing the point and the base
point by equal ones. -/
private lemma ringKrullDim_stalk_fiberHomeo_symm_congr {A B : Scheme.{u}} (q : A ⟶ B)
    {a a' : A} {b b' : B} (ha : a = a') (hb : b = b') (hab : q a = b) (hab' : q a' = b') :
    ringKrullDim ((q.fiber b).presheaf.stalk ((q.fiberHomeo b).symm ⟨a, hab⟩)) =
      ringKrullDim ((q.fiber b').presheaf.stalk ((q.fiberHomeo b').symm ⟨a', hab'⟩)) := by
  subst a'
  subst b'
  rfl

/-- Transporting the residue-field extension at a point along an equality of the image point
leaves the transcendence degree unchanged. -/
lemma trdeg_residueFieldMap_congr {A B : Scheme.{u}} (q : A ⟶ B) (a : A) (b : B)
    (hb : q a = b) :
    letI := ((B.residueFieldCongr hb).inv ≫ q.residueFieldMap a).hom.toAlgebra
    letI := (q.residueFieldMap a).hom.toAlgebra
    Algebra.trdeg ↥(B.residueField b) ↥(A.residueField a) =
      Algebra.trdeg ↥(B.residueField (q a)) ↥(A.residueField a) := by
  subst b
  rfl

/-- A nonempty scheme has a point whose local ring is zero-dimensional: on an affine open
neighbourhood of any point, a minimal prime below the corresponding prime has height zero. -/
public lemma exists_ringKrullDim_stalk_eq_zero (Y : Scheme.{u}) (y₀ : Y) :
    ∃ y : Y, ringKrullDim (Y.presheaf.stalk y) = 0 := by
  obtain ⟨R, j, hj, hjy⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Y) (x := y₀) (show y₀ ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨z, hz⟩ := Set.mem_range.mp hjy.1
  have : z.asIdeal.IsPrime := z.isPrime
  obtain ⟨p, hp, hpz⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal R)) (J := z.asIdeal) bot_le
  have : p.IsPrime := hp.isPrime
  let p' : Spec R := ⟨p, hp.isPrime⟩
  refine ⟨j p', ?_⟩
  rw [ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_isOpenImmersion j, ← idealHeight_eq_coheight R p']
  simp [p', Ideal.height_eq_zero_iff.mpr hp]

/-- A finite summand of `WithBot ℕ∞` can be cancelled from both sides of an equation. -/
public lemma add_right_cancel_of_ne_top_of_ne_bot {a b c : WithBot ℕ∞} (htop : c ≠ ⊤)
    (hbot : c ≠ ⊥) (h : a + c = b + c) : a = b := by
  induction c using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe c =>
    cases c using ENat.recTopCoe with
    | top => exact absurd rfl htop
    | coe c => exact (ENat.WithBot.add_natCast_cancel (c := c)).mp h

/-- A nontrivial ring does not have Krull dimension `⊥`. -/
private lemma ringKrullDim_ne_bot_of_nontrivial (R : Type*) [CommRing R] [Nontrivial R] :
    ringKrullDim R ≠ ⊥ :=
  ringKrullDim_eq_bot_iff_subsingleton.not.mpr (not_subsingleton _)

section Flat

/-- **Stacks Project, Tag 00ON.** For a flat morphism of locally Noetherian schemes, the
dimension of the local ring at a point is the dimension of the local ring at its image plus the
dimension of the local ring of the fibre through the point. -/
@[ega "IV 13.2.4" "special case",
  ega "IV 14.2.1" "special case",
  ega "IV 21.10.7" "special case",
  ega "IV 5.5.2" "special case"]
public theorem ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat {A B : Scheme.{u}}
    (φ : A ⟶ B) [Flat φ] [IsLocallyNoetherian A] [IsLocallyNoetherian B] (a : A) :
    ringKrullDim (A.presheaf.stalk a) =
      ringKrullDim (B.presheaf.stalk (φ a)) +
        ringKrullDim ((φ.fiber (φ a)).presheaf.stalk (φ.asFiber a)) := by
  let : Algebra ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a) :=
    (φ.stalkMap a).hom.toAlgebra
  have hflat : Module.Flat ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a) := by
    change (φ.stalkMap a).hom.Flat
    exact Flat.stalkMap φ a
  have : IsLocalHom
      (algebraMap ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a)) := by
    change IsLocalHom (φ.stalkMap a).hom
    infer_instance
  have hfibre : ringKrullDim
      (ClosedFibre ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a)) =
      ringKrullDim ((φ.fiber (φ a)).presheaf.stalk (φ.asFiber a)) :=
    ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk φ a)
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre _ _ hflat, hfibre]

end Flat

section BaseChange

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- In a fibre product diagram, the two images of a point of `X'` in `S` agree. -/
private lemma apply_eq_of_isPullback (hsq : IsPullback g' f' f g) (x' : X') :
    f (g' x') = g (f' x') := by
  simpa only [← Scheme.Hom.comp_apply] using congrArg (fun r : X' ⟶ S ↦ r.base x') hsq.w

/-- The morphism of fibres induced by a fibre product diagram is flat: it is the base change of
the residue-field extension `κ(g s') ⟶ κ(s')` along the fibre of `f` over `g s'`. -/
private lemma flat_fiberMap_of_isPullback (hsq : IsPullback g' f' f g) (s' : S') :
    Flat (fiberMap f' g' g f hsq.w s') := by
  have hfib : IsPullback (fiberMap f' g' g f hsq.w s') (f'.fiberToSpecResidueField s')
      (f.fiberToSpecResidueField (g s')) (Spec.map (g.residueFieldMap s')) :=
    isPullback_fiberToSpecResidueField_of_isPullback hsq s'
  have hSpec : Flat (Spec.map (g.residueFieldMap s')) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
  exact MorphismProperty.of_isPullback hfib.flip hSpec

/-- The morphism of fibres induced by a fibre product diagram sends the canonical point of `x'`
to the point `g' x'` of the fibre of `f`. -/
public lemma fiberMap_asFiber_eq (hsq : IsPullback g' f' f g) (x' : X')
    (hbase : f (g' x') = g (f' x')) :
    fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x') =
      (f.fiberHomeo (g (f' x'))).symm ⟨g' x', hbase⟩ := by
  apply (f.fiberι (g (f' x'))).isEmbedding.injective
  change (fiberMap f' g' g f hsq.w (f' x') ≫ f.fiberι (g (f' x'))) (f'.asFiber x') = _
  rw [fiberMap_fiberι f' g' g f hsq.w (f' x')]
  simp only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm,
    Scheme.Hom.fiberι_asFiber]

/-- **Stacks Project, Tag 02FY part (2).** In a fibre product diagram with `f` locally of finite
type, the dimension of the local ring at `x'` of the fibre of the induced morphism of fibres, plus
the dimension of the local ring of `X_s` at `x = g' x'`, is the dimension of the local ring of
`X'_{s'}` at `x'`. -/
@[stacks 02FY "local_ring_differences"]
public theorem fiberMap_ringKrullDim_stalk_add_eq (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X') :
    ringKrullDim (((fiberMap f' g' g f hsq.w (f' x')).fiber
            (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))).presheaf.stalk
          ((fiberMap f' g' g f hsq.w (f' x')).asFiber (f'.asFiber x'))) +
        ringKrullDim ((f.fiber (g (f' x'))).presheaf.stalk
          (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))) =
      ringKrullDim ((f'.fiber (f' x')).presheaf.stalk (f'.asFiber x')) := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  have : Flat (fiberMap f' g' g f hsq.w (f' x')) := flat_fiberMap_of_isPullback hsq (f' x')
  have : IsLocallyNoetherian (f.fiber (g (f' x'))) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f (g (f' x'))
  have : IsLocallyNoetherian (f'.fiber (f' x')) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f' (f' x')
  rw [ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat
    (fiberMap f' g' g f hsq.w (f' x')) (f'.asFiber x'), add_comm]

/-- **Stacks Project, Tag 02FY part (2).** The same dimension is the loss of residue-field
transcendence degree: the dimension of the local ring at `x'` of the fibre of the induced
morphism of fibres, plus `trdeg_{κ(s')} κ(x')`, is `trdeg_{κ(s)} κ(x)`. -/
@[stacks 02FY "local_ring_differences"]
public theorem fiberMap_ringKrullDim_stalk_add_trdeg_eq (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X') :
    letI := (f.residueFieldMap (g' x')).hom.toAlgebra
    letI := (f'.residueFieldMap x').hom.toAlgebra
    ringKrullDim (((fiberMap f' g' g f hsq.w (f' x')).fiber
            (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))).presheaf.stalk
          ((fiberMap f' g' g f hsq.w (f' x')).asFiber (f'.asFiber x'))) +
        (Cardinal.toENat (Algebra.trdeg ↥(S'.residueField (f' x')) ↥(X'.residueField x')) :
          WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x'))) :
        WithBot ℕ∞) := by
  let : Algebra ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
    (f.residueFieldMap (g' x')).hom.toAlgebra
  let : Algebra ↥(S'.residueField (f' x')) ↥(X'.residueField x') :=
    (f'.residueFieldMap x').hom.toAlgebra
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  have : IsLocallyNoetherian (f.fiber (g (f' x'))) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f (g (f' x'))
  have hbase := apply_eq_of_isPullback hsq x'
  have hstalk : ringKrullDim ((f.fiber (g (f' x'))).presheaf.stalk
        (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))) =
      ringKrullDim ((f.fiber (f (g' x'))).presheaf.stalk (f.asFiber (g' x'))) := by
    rw [fiberMap_asFiber_eq hsq x' hbase]
    exact ringKrullDim_stalk_fiberHomeo_symm f (g' x') (g (f' x')) hbase
  have hne_top : ringKrullDim ((f.fiber (g (f' x'))).presheaf.stalk
      (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))) ≠ ⊤ := ringKrullDim_ne_top
  have hne_bot : ringKrullDim ((f.fiber (g (f' x'))).presheaf.stalk
      (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))) ≠ ⊥ :=
    ringKrullDim_ne_bot_of_nontrivial _
  refine add_right_cancel_of_ne_top_of_ne_bot hne_top hne_bot ?_
  rw [add_right_comm, fiberMap_ringKrullDim_stalk_add_eq hsq x',
    ← topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f' x',
    topologicalKrullDimAt_fiber_eq_of_isPullback hsq x',
    topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f (g' x'), hstalk, add_comm]

/-- **Stacks Project, Tag 02FY part (2).** The dimension of the local ring of a fibre cannot drop
under base change. -/
@[stacks 02FY "local_ring_differences"]
public theorem ringKrullDim_stalk_fiber_le_of_baseChange (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X') :
    ringKrullDim ((f.fiber (g (f' x'))).presheaf.stalk
        (fiberMap f' g' g f hsq.w (f' x') (f'.asFiber x'))) ≤
      ringKrullDim ((f'.fiber (f' x')).presheaf.stalk (f'.asFiber x')) :=
  (WithBot.le_add_self (ringKrullDim_ne_bot_of_nontrivial _) _).trans_eq
    (fiberMap_ringKrullDim_stalk_add_eq hsq x')

/-- **Stacks Project, Tag 02FY part (2).** The transcendence degree of the residue-field
extension cannot grow under base change. -/
@[stacks 02FY "local_ring_differences"]
public theorem trdeg_residueField_le_of_baseChange (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X') :
    letI := (f.residueFieldMap (g' x')).hom.toAlgebra
    letI := (f'.residueFieldMap x').hom.toAlgebra
    Algebra.trdeg ↥(S'.residueField (f' x')) ↥(X'.residueField x') ≤
      Algebra.trdeg ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) := by
  let : Algebra ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
    (f.residueFieldMap (g' x')).hom.toAlgebra
  let : Algebra ↥(S'.residueField (f' x')) ↥(X'.residueField x') :=
    (f'.residueFieldMap x').hom.toAlgebra
  have : Algebra.EssFiniteType ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f (g' x'))
  have hcoe :
      (Cardinal.toENat (Algebra.trdeg ↥(S'.residueField (f' x')) ↥(X'.residueField x')) :
          WithBot ℕ∞) ≤
        (Cardinal.toENat
          (Algebra.trdeg ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x'))) :
            WithBot ℕ∞) :=
    (WithBot.le_add_self (ringKrullDim_ne_bot_of_nontrivial _) _).trans_eq
      (fiberMap_ringKrullDim_stalk_add_trdeg_eq hsq x')
  exact (Cardinal.toENat_le_iff_of_lt_aleph0
    (trdeg_lt_aleph0 ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')))).mp
      (by exact_mod_cast hcoe)

/-- In a fibre product diagram, given `s'` in `S'` and `x` in `X` with the same image in `S`,
there is a common lift `x'` in `X'` at which the fibre of the induced morphism of fibres has a
zero-dimensional local ring. -/
public lemma exists_pullback_point_ringKrullDim_stalk_fiberMap_eq_zero
    (hpb : IsPullback g' f' f g) (s' : S') (x : X) (h : f x = g s') :
    ∃ (x' : X') (_hx : g' x' = x) (_hs' : f' x' = s'),
      ringKrullDim (((fiberMap f' g' g f hpb.w (f' x')).fiber
            (fiberMap f' g' g f hpb.w (f' x') (f'.asFiber x'))).presheaf.stalk
          ((fiberMap f' g' g f hpb.w (f' x')).asFiber (f'.asFiber x'))) = 0 := by
  obtain ⟨x₀, hx₀, hs₀⟩ := Scheme.exists_preimage_of_isPullback hpb x s' h
  let φ := fiberMap f' g' g f hpb.w s'
  let y₀ : f'.fiber s' := (f'.fiberHomeo s').symm ⟨x₀, hs₀⟩
  let t : f.fiber (g s') := (f.fiberHomeo (g s')).symm ⟨x, h⟩
  have hφ_under (a : f'.fiber s') : f.fiberι (g s') (φ a) = g' (f'.fiberι s' a) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      show φ ≫ f.fiberι (g s') = f'.fiberι s' ≫ g' from fiberMap_fiberι f' g' g f hpb.w s']
  have hφy₀ : φ y₀ = t := by
    apply (f.fiberι (g s')).isEmbedding.injective
    rw [hφ_under]
    simp [y₀, t, hx₀]
  obtain ⟨z, hz⟩ :=
    exists_ringKrullDim_stalk_eq_zero (φ.fiber t) ((φ.fiberHomeo t).symm ⟨y₀, hφy₀⟩)
  let y : f'.fiber s' := φ.fiberι t z
  let x' : X' := f'.fiberι s' y
  have hs' : f' x' = s' := (f'.fiberHomeo s' y).2
  have hφy : φ y = t := (φ.fiberHomeo t z).2
  have hx : g' x' = x := by
    rw [← hφ_under y, hφy]
    simp [t]
  let y' : f'.fiber s' := (f'.fiberHomeo s').symm ⟨x', hs'⟩
  have hy : y' = y := by
    apply (f'.fiberι s').isEmbedding.injective
    simp [y', x']
  have hzero : ringKrullDim ((φ.fiber (φ y')).presheaf.stalk (φ.asFiber y')) = 0 := by
    have hφy' : φ y' = t := (congrArg φ hy).trans hφy
    rw [← ringKrullDim_stalk_fiberHomeo_symm φ y' t hφy']
    have he : (φ.fiberHomeo t).symm ⟨y', hφy'⟩ = z := by
      apply (φ.fiberι t).isEmbedding.injective
      simp [hy, y]
    rwa [he]
  have hcomparison_transport (s : S') (e : f' x' = s) :
      ringKrullDim (((fiberMap f' g' g f hpb.w s).fiber
            ((fiberMap f' g' g f hpb.w s) ((f'.fiberHomeo s).symm ⟨x', e⟩))).presheaf.stalk
          ((fiberMap f' g' g f hpb.w s).asFiber ((f'.fiberHomeo s).symm ⟨x', e⟩))) =
        ringKrullDim (((fiberMap f' g' g f hpb.w (f' x')).fiber
            (fiberMap f' g' g f hpb.w (f' x') (f'.asFiber x'))).presheaf.stalk
          ((fiberMap f' g' g f hpb.w (f' x')).asFiber (f'.asFiber x'))) := by
    subst s
    rfl
  exact ⟨x', hx, hs', (hcomparison_transport s' hs').symm.trans hzero⟩

/-- **Stacks Project, Tag 02FY part (3).** In a fibre product diagram with `f` locally of finite
type, let `s'` be a point of `S'` and `x` a point of `X` with the same image `s` in `S`. Then
there is a common lift `x'` of `x` and `s'` to `X'` at which neither the dimension of the local
ring of the fibre nor the transcendence degree of the residue-field extension changes. -/
@[stacks 02FY "zero_difference_lift"]
public theorem exists_pullback_point_preserving_fibre_dimension_and_trdeg
    (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] (s' : S') (x : X) (h : f x = g s') :
    ∃ (x' : X') (_hx : g' x' = x) (hs' : f' x' = s'),
      ringKrullDim ((f'.fiber s').presheaf.stalk ((f'.fiberHomeo s').symm ⟨x', hs'⟩)) =
          ringKrullDim ((f.fiber (g s')).presheaf.stalk
            ((f.fiberHomeo (g s')).symm ⟨x, h⟩)) ∧
        (letI := ((S.residueFieldCongr h).inv ≫ f.residueFieldMap x).hom.toAlgebra
         letI := ((S'.residueFieldCongr hs').inv ≫ f'.residueFieldMap x').hom.toAlgebra
         Algebra.trdeg ↥(S.residueField (g s')) ↥(X.residueField x) =
           Algebra.trdeg ↥(S'.residueField s') ↥(X'.residueField x')) := by
  obtain ⟨x', hx, hs', hzero⟩ :=
    exists_pullback_point_ringKrullDim_stalk_fiberMap_eq_zero hpb s' x h
  have ebase := apply_eq_of_isPullback hpb x'
  refine ⟨x', hx, hs', ?_, ?_⟩
  · have hd := fiberMap_ringKrullDim_stalk_add_eq hpb x'
    rw [hzero, zero_add, fiberMap_asFiber_eq hpb x' ebase] at hd
    rw [ringKrullDim_stalk_fiberHomeo_symm f' x' s' hs']
    exact hd.symm.trans
      (ringKrullDim_stalk_fiberHomeo_symm_congr f hx (congrArg g hs') ebase h)
  · have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hpb inferInstance
    let : Algebra ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
      (f.residueFieldMap (g' x')).hom.toAlgebra
    let : Algebra ↥(S'.residueField (f' x')) ↥(X'.residueField x') :=
      (f'.residueFieldMap x').hom.toAlgebra
    have ht := fiberMap_ringKrullDim_stalk_add_trdeg_eq hpb x'
    dsimp only at ht
    rw [hzero, zero_add] at ht
    have : Algebra.EssFiniteType ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
      RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f (g' x'))
    have : Algebra.EssFiniteType ↥(S'.residueField (f' x')) ↥(X'.residueField x') :=
      RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f' x')
    have hcard := (Cardinal.toENat_eq_iff_of_le_aleph0 (trdeg_lt_aleph0 _ _).le
      (trdeg_lt_aleph0 _ _).le).mp (WithBot.coe_eq_coe.mp ht)
    calc
      _ = @Algebra.trdeg _ _ _ _ (f.residueFieldMap x).hom.toAlgebra :=
        trdeg_residueFieldMap_congr f x (g s') h
      _ = Algebra.trdeg ↥(S.residueField (f (g' x'))) ↥(X.residueField (g' x')) :=
        congrArg (fun a : X ↦ @Algebra.trdeg _ _ _ _ (f.residueFieldMap a).hom.toAlgebra) hx.symm
      _ = Algebra.trdeg ↥(S'.residueField (f' x')) ↥(X'.residueField x') := hcard.symm
      _ = _ := (trdeg_residueFieldMap_congr f' x' s' hs').symm

end BaseChange

end AlgebraicGeometry

end
