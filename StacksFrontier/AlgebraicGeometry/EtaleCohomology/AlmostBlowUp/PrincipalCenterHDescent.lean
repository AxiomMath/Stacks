module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.DerivedHDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.PrincipalCenter
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking
import StacksCore.Tactic.StacksAttribute

/-!
# Almost blow up squares with a principal centre and the h topology

Let `B` be a big h site containing a scheme `S`, so that the big h category over `S` carries the
h topology `J`, and let `J' ≤ J` be a coarser topology on the same category — the fppf topology
in the source, since an fppf covering is an h covering. A sheaf of rings `𝒪` for `J` is then
also a sheaf of rings for `J'`, and the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})` whose derived direct image is `Rε_*`.

Stacks 0EWR says that an object `K` of `D⁺(𝒪_{J'})` lies in the essential image of `Rε_*` if and
only if the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is a
quasi-isomorphism for every almost blow up square of the two shapes of More on Flatness,
Examples 0EVG and 0EVH. This file proves the "only if" direction for the squares of the first
shape: those of

```
E = Spec(A/(fA + J)) ⟶ X' = Spec(A/J)
      ↓                      ↓
Z = Spec(A/fA)        ⟶ X = Spec(A)
```

for a ring `A`, an element `f` of `A` and a finitely generated ideal `J` of `A` annihilated by a
power of `f`.

## Main definitions

* `AlgebraicGeometry.IsPrincipalCenterModelPair`: a modification and a centre with a common
  base have the shape of More on Flatness, Example 0EVG.

## Main results

* `AlgebraicGeometry.isAlmostBlowUpSquare_isIso_comp`: precomposing the modification of an
  almost blowup square with an isomorphism gives an almost blowup square with the same centre.
* `AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair`: a pair of
  morphisms with the shape of More on Flatness, Example 0EVG is the modification and the centre
  of an almost blowup square.
* `AlgebraicGeometry.isCSquareIso_of_essImage_principalCenterModelPair_bigH`: **Stacks 0EWR**,
  the "only if" direction for the almost blow up squares of More on Flatness, Example 0EVG.

## Scope

Only the "only if" direction of Stacks 0EWR is proved here, and only for the squares of More on
Flatness, Example 0EVG; the attribute carries that part as a scoped clause.

In that direction the quantifier of the source ranges over squares that are almost blowup
squares, so the direction is a consequence of Stacks 0EWN — which holds for *every* almost
blowup square — once the squares named by the source are known to be almost blowup squares. For
Example 0EVG that is `AlgebraicGeometry.isAlmostBlowUpSquare_quotient_of_pow_mul_eq_zero`, and
transporting it along an isomorphism of the base and of the modification is what the two lemmas
preceding the theorem do. The corresponding statement for Example 0EVH is also available, as
`Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase`, so the same argument applies to
that shape; only the squares of Example 0EVG are treated here.

The "if" direction is the content of the source's proof, which deduces it from Stacks 0F18 —
available as `Stacks.Cohomology.MayerVietoris.essImage_iff_forall_isCSquareIso` — whose
detection hypothesis for the family of squares of Examples 0EVG and 0EVH is More on Flatness,
Lemma 0EVI. That lemma is not formalized, and neither is More on Flatness, Proposition 0EVF on
which its proof rests.

## Implementation notes

As in `AlgebraicGeometry.isCSquareIso_of_essImage_almostBlowUpSquare_bigH` the coarser topology
is an arbitrary one with the proof that it is coarser as a hypothesis, `Rε_*` is an arbitrary
right derived functor of `ε_*` with its unit, and the square is presented as an object of
`CategoryTheory.Square` whose vertices are, in order, the exceptional corner, the modification,
the centre and the base, with the requirement that the square of underlying schemes be
cartesian.

The shape of Example 0EVG is recognized up to isomorphism: an isomorphism of the base with
`Spec(A)` carrying the modification and the centre to the model pair, as isomorphisms of schemes
over `Spec(A)`. The transport of `AlgebraicGeometry.IsAlmostBlowUpSquare` to a square of that
shape goes through the base change of Stacks 0EV7 along that isomorphism of bases, after which
the modification differs from the given one by an isomorphism over the base; such a square being
a pullback is `CategoryTheory.IsPullback.of_vert_isIso`.

Precomposing the modification with an isomorphism `g` leaves the centre, hence the first
condition, untouched; the inverse-image centre is pulled back along `g`, properness and finite
presentation are stable under composition with an isomorphism, and the blowup condition
transports because `g` restricts to an isomorphism over the complement of the exceptional
corner, so `AlgebraicGeometry.supportedSectionsIdeal_map_of_restrict_isIso` applies — the same
step as in the proof of Stacks 0EV8.

## References

* [Stacks Project, Tag 0EWR](https://stacks.math.columbia.edu/tag/0EWR)
* [Stacks Project, Tag 0EWN](https://stacks.math.columbia.edu/tag/0EWN)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Precomposing the modification of an almost blowup square with an isomorphism gives again an
almost blowup square with the same centre. -/
theorem isAlmostBlowUpSquare_isIso_comp {X X' X'' : Scheme.{u}} (I : X.IdealSheafData)
    {b : X' ⟶ X} (h : IsAlmostBlowUpSquare I b) (g : X'' ⟶ X') [IsIso g] :
    IsAlmostBlowUpSquare I (g ≫ b) := by
  refine ⟨h.center_finitePresentation, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isLocallyPrincipal_comap g (I.comap b) h.exceptional_locallyPrincipal
  · have : IsProper b := h.proper
    infer_instance
  · refine FinitePresentation.mk ?_ ?_ ?_
    · have : LocallyOfFinitePresentation b := h.finitePresentation.locallyOfFinitePresentation
      infer_instance
    · have : QuasiCompact b := h.finitePresentation.quasiCompact
      infer_instance
    · have : QuasiSeparated b := h.finitePresentation.quasiSeparated
      infer_instance
  · let E : Set X' := ((I.comap b).support : Set X')
    have hEclosed : IsClosed E := (I.comap b).support.isClosed
    have hsupp : ((I.comap (g ≫ b)).support : Set X'') = g.base ⁻¹' E := by
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.support_comap]
      rfl
    have hmap : (supportedSectionsIdeal ((I.comap (g ≫ b)).support : Set X'')).map g =
        supportedSectionsIdeal E := by
      rw [hsupp]
      exact supportedSectionsIdeal_map_of_restrict_isIso g E hEclosed inferInstance
    let L := supportedSectionsIdeal ((I.comap (g ≫ b)).support : Set X'')
    let Kd := supportedSectionsIdeal E
    let e0 : Over.mk Kd.subschemeι ≅ Over.mk (L.subschemeι ≫ g) :=
      idealMapSubschemeIso g L Kd hmap
    let e : Over.mk (Kd.subschemeι ≫ b) ≅ Over.mk (L.subschemeι ≫ g ≫ b) :=
      Over.isoMk ((Over.forget X').mapIso e0)
        (by simpa [Category.assoc] using congrArg (fun k => k ≫ b) (Over.w e0.hom))
    exact ⟨e.symm ≪≫ h.blowUp.some⟩

/-- The modification and the centre of the almost blow up square of More on Flatness, Example
0EVG: for a ring `A`, an element `f` of `A` and a finitely generated ideal `J` of `A` annihilated
by a power of `f`, the modification is `Spec(A/J) ⟶ Spec(A)` and the centre is the closed
subscheme cut out by `f`.

A pair of morphisms with a common target has that shape when some isomorphism of the target with
`Spec(A)` carries the pair to the model pair, as schemes over `Spec(A)`.

The same notion is written out a second time, as
`AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel` in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion`. The
two are not interchangeable as they stand: this one asks for isomorphisms in the slice over
`Spec(A)`, that one factors the condition through `IsOneGeneratorAlmostBlowUpModel`'s
`IsModelPairOverBase`, which asks for three isomorphisms of schemes and two commuting squares,
and neither module reaches the other. Identifying them would need a bridge lemma. -/
def IsPrincipalCenterModelPair {X X' Z : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) : Prop :=
  ∃ (A : Type u) (hA : CommRing A),
    letI := hA
    ∃ (f : A) (J : Ideal A), J.FG ∧ (∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) ∧
      ∃ iX : X ≅ Spec (.of A),
        Nonempty (Over.mk (b ≫ iX.hom) ≅
            Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ∧
          Nonempty (Over.mk (z ≫ iX.hom) ≅
            Over.mk (Scheme.IdealSheafData.ofIdealTop
              (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subschemeι)

/-- The model pair of More on Flatness, Example 0EVG has the shape of that example. -/
theorem isPrincipalCenterModelPair_model (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (hJ : J.FG) (hann : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    IsPrincipalCenterModelPair (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subschemeι := by
  refine ⟨A, inferInstance, f, J, hJ, hann, Iso.refl _, ⟨?_⟩, ⟨?_⟩⟩
  · exact Over.isoMk (Iso.refl _) (by simp)
  · exact Over.isoMk (Iso.refl _) (by simp)

/-- An isomorphism `b ≫ i ≅ m` in the slice over the target of `i` gives a pullback square. -/
private theorem isPullback_of_overIso {X Y P Q : Scheme.{u}} (i : X ⟶ Y) [IsIso i] {b : P ⟶ X}
    {m : Q ⟶ Y} (e : Over.mk (b ≫ i) ≅ Over.mk m) : IsPullback b e.hom.left i m :=
  have : IsIso e.hom.left := (Over.forget Y).map_isIso e.hom
  IsPullback.of_vert_isIso ⟨(Over.w e.hom).symm⟩

/-- A pair of morphisms with the shape of More on Flatness, Example 0EVG is the modification and
the centre of an almost blowup square.

By Stacks 0EVG the model pair is one; an almost blowup square stays one after the base change
along the isomorphism of bases (Stacks 0EV7), and then after precomposing the modification with
an isomorphism over the base. -/
theorem exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair {X X' Z : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (h : IsPrincipalCenterModelPair b z) :
    ∃ I : X.IdealSheafData,
      IsAlmostBlowUpSquare I b ∧ Nonempty (Over.mk z ≅ Over.mk I.subschemeι) := by
  obtain ⟨A, hA, f, J, hJfg, hann, iX, ⟨eb⟩, ⟨ez⟩⟩ := h
  let := hA
  set Im : (Spec (.of A)).IdealSheafData := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))
  set bm := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hmodel : IsAlmostBlowUpSquare Im bm :=
    isAlmostBlowUpSquare_quotient_of_pow_mul_eq_zero A f J hJfg hann
  have hpb := isPullback_of_overIso iX.hom eb
  have hpz := isPullback_of_overIso iX.hom ez
  refine ⟨Im.comap iX.hom, ?_, ?_⟩
  · have h0 : IsAlmostBlowUpSquare (Im.comap iX.hom) (pullback.fst iX.hom bm) :=
      isAlmostBlowUpSquare_baseChange Im bm iX.hom hmodel
    have h1 : IsAlmostBlowUpSquare (Im.comap iX.hom)
        (hpb.isoPullback.hom ≫ pullback.fst iX.hom bm) :=
      isAlmostBlowUpSquare_isIso_comp _ h0 hpb.isoPullback.hom
    rwa [hpb.isoPullback_hom_fst] at h1
  · let ez' : Over.mk z ≅ Over.mk (pullback.fst iX.hom Im.subschemeι) :=
      Over.isoMk hpz.isoPullback (by simp)
    let ec : Over.mk (Im.comap iX.hom).subschemeι ≅
        Over.mk (pullback.fst iX.hom Im.subschemeι) :=
      Over.isoMk (Im.comapIso iX.hom)
        (by simp [Scheme.IdealSheafData.comapIso_hom_fst Im iX.hom])
    exact ⟨ez' ≪≫ ec.symm⟩

/-- **Stacks 0EWR, the "only if" direction for the almost blow up squares of More on Flatness,
Example 0EVG.** Let `J' ≤ J` be a topology coarser than the h topology on the big h category
over `S` — the fppf topology in the source — and let `𝒪` be a sheaf of rings for the h topology,
so that the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. Let `K` be an object of `D(𝒪_{J'})` in the essential image
of the derived direct image `Rε_*`. Then for every almost blow up square of the shape of More on
Flatness, Example 0EVG in the big h category over `S` the canonical Mayer–Vietoris comparison
`c^K_{X,X',Z,E}` of Stacks 0F16 for the coarser topology is a quasi-isomorphism.

The squares named by the source are almost blow up squares, by Stacks 0EVG transported along the
isomorphism recognizing the shape, so this is Stacks 0EWN. -/
@[stacks 0EWR "only if, for the almost blow up squares of More on Flatness, Example 0EVG"]
theorem isCSquareIso_of_essImage_principalCenterModelPair_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r})
    {J' : GrothendieckTopology (BigHOver B S hS)} (hJ : J' ≤ BigHOver.topology B S hS)
    [HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{v}]
    [(BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [UnivLE.{u + 1, v}] [UnivLE.{u, v}] [UnivLE.{r, v}]
    (Rε : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (Stacks.Sites.CoarserTopology.modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
      (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (hK : Rε.essImage K)
    (sq : Square (BigHOver B S hS))
    (hmodel : IsPrincipalCenterModelPair ((BigHOver.toScheme B S hS).map sq.f₂₄)
      ((BigHOver.toScheme B S hS).map sq.f₃₄))
    (hSquare : (sq.map (BigHOver.toScheme B S hS)).IsPullback) :
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
      sq).IsCSquareIso K := by
  obtain ⟨I, hb, hZ⟩ := exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair _ _ hmodel
  exact isCSquareIso_of_essImage_almostBlowUpSquare_bigH.{u, v, r}
    B S hS O hJ Rε η K hK sq I hb hZ hSquare

end AlgebraicGeometry

end
