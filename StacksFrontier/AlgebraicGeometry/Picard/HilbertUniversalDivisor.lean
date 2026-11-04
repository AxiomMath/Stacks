module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOfCurve

/-!
# The universal divisor on the Hilbert scheme of points of a curve

Let `X` be a geometrically irreducible smooth proper curve over a field `k`, let `d ≥ 0`, and let
`H'` represent `Hilb^{d+1}_{X/k}` with universal family `D_univ ⊆ X ×_k H'`. Stacks Tag 0B9J
records three facts about it:

1. `D_univ` is a relative effective Cartier divisor on `X ×_k H'` over `H'` (Stacks Tag 0B9D);
   in particular it is an effective Cartier divisor, with invertible sheaf `𝒪(D_univ)`
   (`Stacks.Divisors.invertibleSheaf_isInvertible`);
2. `D_univ` is isomorphic, as a scheme, to `H ×_k X` where `H` represents `Hilb^d_{X/k}`: the
   isomorphism is the incidence morphism of point addition (proof of Stacks Tag 0B9G);
3. if `[D]` is the `k`-rational point of `H'` classifying an effective Cartier divisor
   `D ⊆ X` of degree `d + 1`, the restriction of `𝒪(D_univ)` to the fibre `X ≅ X ×_k [D]` is
   `𝒪_X(D)`.

## Main definitions

* `Stacks.Hilbert.universalDivisorIso` — the isomorphism `H ×_k X ≅ D_univ`.

## Main results

* `Stacks.Hilbert.isRelativeEffectiveCartierDivisor_universalFamily` — fact (1).
* `Stacks.Hilbert.universalDivisorIso_hom_comp_snd` and
  `Stacks.Hilbert.universalDivisorIso_hom_comp_fst` — fact (2): under the isomorphism the
  projection of `D_univ` to `H'` is point addition and its projection to `X` is the second
  projection.
* `Stacks.Hilbert.nonempty_pullback_invertibleSheaf_universalFamily_iso` — fact (3).

## Implementation notes

*Why the statements quantify over the representing schemes.* Stacks Tag 0B9J is a remark about
"the" Hilbert scheme `underline{Hilb}^{d+1}_{X/k}` and its universal object, which exist by
Stacks Tag 0B9I (1) and are unique up to unique isomorphism
(`Stacks.Hilbert.RepresentsHilbertFunctorOfRank.isoOver`). Every assertion of the remark is a
property of a representing scheme together with its universal family, and it is proved here for
every representing scheme; the representing data is the object the remark is about, not an
input that the source proves elsewhere.

*The rational point and its divisor.* A `k`-rational point of `H'` is a morphism `p` from
`Spec k`, viewed over itself, to `H'`. The fibre of `X ×_k H'` over it is identified with `X`
by a morphism `g : X ⟶ X ×_k H'` with components `𝟙 X` and `X ⟶ Spec k ⟶ H'`, and the divisor
classified by `p` is `g⁻¹ D_univ`.

## References

* [Stacks Project, Tag 0B9J](https://stacks.math.columbia.edu/tag/0B9J)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- A lift `φ` of the incidence morphism of point addition `g` composes with the inclusion of the
universal family and the projections to `H'` and to `X` to give `g` and the point component. -/
private theorem comp_subschemeι_comp_eq {S : Scheme.{u}} {X H H' : Over S} {n : ℕ}
    {hH' : RepresentsHilbertFunctorOfRank X H' n} {g : H ⨯ X ⟶ H'}
    {φ : (H ⨯ X).left ⟶ (hH'.family (𝟙 H')).ideal.subscheme}
    (hφ : φ ≫ (hH'.family (𝟙 H')).ideal.subschemeι =
      pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g) :
    φ ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ ((Over.pullback H'.hom).obj X).hom = g.left ∧
      φ ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.fst X.hom H'.hom =
        (prod.snd : H ⨯ X ⟶ X).left := by
  refine ⟨?_, ?_⟩ <;> rw [← Category.assoc, hφ, Category.assoc]
  · rw [familyBaseChangeMap_comp_hom, ← Category.assoc, pointGraph_comp_hom, Category.id_comp]
  · rw [familyBaseChangeMap_comp_fst, pointGraph_comp_fst]

section Incidence

variable {S : Scheme.{u}} {X H H' : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
  {hH : RepresentsHilbertFunctorOfRank X H d}
  {hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)} {g : H ⨯ X ⟶ H'}

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The graph of the universal point of `H ×_S X`, pushed into `X ×_S H'` along a point-addition
morphism `g`, lies in the universal degree-`(d+1)` family. -/
theorem ker_subschemeι_le_ker_incidence (hg : IsPointAddition hH hH' g) :
    (hH'.family (𝟙 H')).ideal.subschemeι.ker ≤
      (pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g).ker := by
  rw [(hH'.family (𝟙 H')).ideal.ker_subschemeι, ← Scheme.IdealSheafData.map_ker]
  refine Scheme.IdealSheafData.le_map_iff_comap_le.mpr ?_
  have h := hH'.naturality g (𝟙 H')
  rw [Category.comp_id] at h
  rw [← h]
  have h2 := hg.family_ideal_le (H ⨯ X) (𝟙 _)
  rw [Category.id_comp] at h2
  exact h2

/-- A morphism `φ : H ×_S X ⟶ D_univ` lifting the incidence morphism of point addition hits every
point of the universal family: a point of `D_univ` comes from a point of `H ×_S X` by
subtracting the graph of the point (Stacks Tag 0B9F). -/
private theorem exists_comp_eq_of_comp_subschemeι_eq (hg : IsPointAddition hH hH' g)
    {φ : (H ⨯ X).left ⟶ (hH'.family (𝟙 H')).ideal.subscheme}
    (hφ : φ ≫ (hH'.family (𝟙 H')).ideal.subschemeι =
      pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g)
    {T : Over S} (t : T ⟶ H') (x : T ⟶ X) (v : T.left ⟶ (hH'.family (𝟙 H')).ideal.subscheme)
    (hv : v ≫ (hH'.family (𝟙 H')).ideal.subschemeι = pointGraph X T x ≫ familyBaseChangeMap X t) :
    ∃ g' : T ⟶ H ⨯ X, g'.left ≫ φ = v := by
  have hle : (hH'.family t).ideal ≤ pointIdeal X T x := by
    have h := hH'.naturality t (𝟙 H')
    rw [Category.comp_id] at h
    rw [h, pointIdeal]
    refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
    rw [Scheme.IdealSheafData.map_ker, ← hv]
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using
      Scheme.Hom.le_ker_comp v (hH'.family (𝟙 H')).ideal.subschemeι
  obtain ⟨g', hgt, hgx⟩ : ∃ g' : T ⟶ H ⨯ X, g' ≫ g = t ∧ g' ≫ prod.snd = x := by
    obtain ⟨D', hD'⟩ := exists_familyAddPoint_eq (hH'.family t) x hle
    refine ⟨prod.lift (hH.family.symm D') x, ?_, prod.lift_snd _ _⟩
    refine hH'.family.injective (HilbertFamily.ext ?_)
    rw [hg T (prod.lift (hH.family.symm D') x), prod.lift_fst, prod.lift_snd,
      Equiv.apply_symm_apply]
    exact hD'.symm
  refine ⟨g', (cancel_mono (hH'.family (𝟙 H')).ideal.subschemeι).mp ?_⟩
  rw [Category.assoc, hφ, hv]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst]
    rw [← Over.comp_left, hgx]
  · simp only [Category.assoc, familyBaseChangeMap_comp_snd, pointGraph_comp_snd_assoc]
    rw [← Over.comp_left, hgt]

/-- A morphism `φ : H ×_S X ⟶ D_univ` lifting the incidence morphism of point addition is a
monomorphism: a point of `H ×_S X` is determined by its image under point addition and its point
component. -/
private theorem mono_of_comp_subschemeι_eq (hg : IsPointAddition hH hH' g)
    {φ : (H ⨯ X).left ⟶ (hH'.family (𝟙 H')).ideal.subscheme}
    (hφ : φ ≫ (hH'.family (𝟙 H')).ideal.subschemeι =
      pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g) : Mono φ := by
  obtain ⟨hφhom, hφfst⟩ := comp_subschemeι_comp_eq hφ
  refine ⟨fun u u' h => ?_⟩
  have ha : u ≫ g.left = u' ≫ g.left := by
    simpa only [Category.assoc, hφhom] using congrArg (fun m => m ≫
      (hH'.family (𝟙 H')).ideal.subschemeι ≫ ((Over.pullback H'.hom).obj X).hom) h
  have hxl : u ≫ (prod.snd : H ⨯ X ⟶ X).left = u' ≫ (prod.snd : H ⨯ X ⟶ X).left := by
    simpa only [Category.assoc, hφfst] using congrArg (fun m => m ≫
      (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.fst X.hom H'.hom) h
  have hb : u' ≫ (H ⨯ X).hom = u ≫ (H ⨯ X).hom := by
    rw [← Over.w g, ← Category.assoc, ← Category.assoc, ha]
  exact congrArg Over.Hom.left
    (hg.eq_of_comp_eq (T := Over.mk (u ≫ (H ⨯ X).hom))
      (Over.homMk u (by simp only [Over.mk_hom]))
      (Over.homMk u' (by simpa only [Over.mk_hom] using hb))
      (Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.homMk_left] using ha))
      (Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.homMk_left] using hxl)))

/-- **The incidence morphism of point addition is an isomorphism** onto the universal
degree-`(d+1)` family: it is a monomorphism, a point of `H ×_S X` being determined by its image
under point addition and its point component, and every point of the universal family comes from
a point of `H ×_S X` by subtracting the graph of the point (Stacks Tag 0B9F). -/
theorem isIso_lift_incidence (hg : IsPointAddition hH hH' g) :
    IsIso (IsClosedImmersion.lift (hH'.family (𝟙 H')).ideal.subschemeι
      (pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g)
      (ker_subschemeι_le_ker_incidence hg)) := by
  have hφ := IsClosedImmersion.lift_fac (hH'.family (𝟙 H')).ideal.subschemeι
    (pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X g)
    (ker_subschemeι_le_ker_incidence hg)
  have := mono_of_comp_subschemeι_eq hg hφ
  refine isIso_of_yoneda_map_bijective _ fun T =>
    ⟨fun _ _ h => (cancel_mono _).mp h, fun v => ?_⟩
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_comp_subschemeι_eq hg hφ
    (T := Over.mk (v ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.snd X.hom H'.hom ≫
      H'.hom))
    (Over.homMk (v ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.snd X.hom H'.hom)
      (by simp only [Over.mk_hom, Category.assoc]))
    (Over.homMk (v ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.fst X.hom H'.hom)
      (by simp only [Over.mk_hom, Category.assoc, pullback.condition]))
    v (by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst,
          Over.homMk_left]
      · simp only [Category.assoc, familyBaseChangeMap_comp_snd, pointGraph_comp_snd_assoc,
          Over.homMk_left])
  exact ⟨g'.left, hg'⟩

end Incidence

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The identification of `X` with the fibre of `X ×_k H'` over a rational point `p`: a section
`g` with components `𝟙 X` and `X ⟶ Spec k ⟶ H'` is the inverse of the canonical isomorphism
`X ×_k Spec k ≅ X` followed by the base-change map along `p`. -/
private theorem fiber_maps {H : Over (Spec (.of k))} (p : Over.mk (𝟙 (Spec (.of k))) ⟶ H)
    (g : X ⟶ pullback f H.hom) (hgX : g ≫ pullback.fst f H.hom = 𝟙 X)
    (hgH : g ≫ pullback.snd f H.hom = f ≫ p.left) :
    g = (asIso (pullback.fst f (𝟙 (Spec (.of k))))).inv ≫
      familyBaseChangeMap (Over.mk f) p := by
  refine pullback.hom_ext ?_ ?_
  · have h1 : familyBaseChangeMap (Over.mk f) p ≫ pullback.fst f H.hom =
        pullback.fst f (𝟙 (Spec (.of k))) :=
      familyBaseChangeMap_comp_fst (Over.mk f) p
    rw [hgX, Category.assoc, h1, asIso_inv, IsIso.inv_hom_id]
  · have h2 : familyBaseChangeMap (Over.mk f) p ≫ pullback.snd f H.hom =
        pullback.snd f (𝟙 (Spec (.of k))) ≫ p.left :=
      familyBaseChangeMap_comp_snd (Over.mk f) p
    have h3 : pullback.snd f (𝟙 (Spec (.of k))) = pullback.fst f (𝟙 (Spec (.of k))) ≫ f := by
      rw [pullback.condition, Category.comp_id]
    rw [hgH, Category.assoc, h2, h3, Category.assoc, asIso_inv, IsIso.inv_hom_id_assoc]

/-- **Stacks Project, Tag 0B9J, fact (1).** The universal family on a scheme representing
`Hilb^{d+1}_{X/k}` is a relative effective Cartier divisor over it; stated for every degree `d`,
which the proof does not distinguish. -/
theorem isRelativeEffectiveCartierDivisor_universalFamily [IsCurve k f] [Smooth f] {d : ℕ}
    {H' : Over (Spec (.of k))} (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' d) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor
      ((Over.pullback H'.hom).obj (Over.mk f)).hom (hH'.family (𝟙 H')).ideal := by
  let : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve f
  let : SmoothOfRelativeDimension 1 ((Over.pullback H'.hom).obj (Over.mk f)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f H'.hom) inferInstance
  let : Stacks.Morphisms.IsFiniteLocallyFree ((hH'.family (𝟙 H')).ideal.subschemeι ≫
      ((Over.pullback H'.hom).obj (Over.mk f)).hom) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d
      (hH'.family (𝟙 H')).isFiniteLocallyFreeOfRank
  exact isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree _ _

/-- **Stacks Project, Tag 0B9J, fact (2).** The universal family `D_univ` on a scheme `H'`
representing `Hilb^{d+1}_{X/k}` is isomorphic to `H ×_k X`, where `H` represents
`Hilb^d_{X/k}`: the isomorphism is the incidence morphism of point addition, the lift of the graph
of the universal point, pushed along point addition, to `D_univ`. It is a monomorphism, and every
point of `D_univ` comes from a point of `H ×_k X` by subtracting the graph of the point (Stacks
Tag 0B9F). -/
def universalDivisorIso [IsCurve k f] [Smooth f] [IsProper f] {d : ℕ}
    {H H' : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    (H ⨯ Over.mk f).left ≅ (hH'.family (𝟙 H')).ideal.subscheme :=
  letI : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  letI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  haveI := isIso_lift_incidence (isPointAddition_addPoint hH hH')
  asIso (IsClosedImmersion.lift (hH'.family (𝟙 H')).ideal.subschemeι
    (pointGraph (Over.mk f) (H ⨯ Over.mk f) prod.snd ≫
      familyBaseChangeMap (Over.mk f) (addPoint hH hH'))
    (ker_subschemeι_le_ker_incidence (isPointAddition_addPoint hH hH')))

/-- The underlying morphism of `Stacks.Hilbert.universalDivisorIso` is the incidence morphism. -/
theorem universalDivisorIso_hom [IsCurve k f] [Smooth f] [IsProper f] {d : ℕ}
    {H H' : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    letI : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
    letI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
    (universalDivisorIso f hH hH').hom =
      IsClosedImmersion.lift (hH'.family (𝟙 H')).ideal.subschemeι
        (pointGraph (Over.mk f) (H ⨯ Over.mk f) prod.snd ≫
          familyBaseChangeMap (Over.mk f) (addPoint hH hH'))
        (ker_subschemeι_le_ker_incidence (isPointAddition_addPoint hH hH')) :=
  rfl

/-- Under `Stacks.Hilbert.universalDivisorIso`, the inclusion of `D_univ` is the incidence
morphism of point addition. -/
private theorem universalDivisorIso_hom_comp_subschemeι [IsCurve k f] [Smooth f] [IsProper f]
    {d : ℕ} {H H' : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    letI : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
    letI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
    (universalDivisorIso f hH hH').hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι =
      pointGraph (Over.mk f) (H ⨯ Over.mk f) prod.snd ≫
        familyBaseChangeMap (Over.mk f) (addPoint hH hH') := by
  rw [universalDivisorIso_hom]
  exact IsClosedImmersion.lift_fac _ _ _

/-- Under `Stacks.Hilbert.universalDivisorIso`, the projection of `D_univ` to `H'` is point
addition `H ×_k X ⟶ H'`. -/
theorem universalDivisorIso_hom_comp_snd [IsCurve k f] [Smooth f] [IsProper f] {d : ℕ}
    {H H' : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    letI : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
    letI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
    (universalDivisorIso f hH hH').hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫
        pullback.snd f H'.hom = (addPoint hH hH').left := by
  let : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  let : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  exact (comp_subschemeι_comp_eq (universalDivisorIso_hom_comp_subschemeι f hH hH')).1

/-- Under `Stacks.Hilbert.universalDivisorIso`, the projection of `D_univ` to `X` is the second
projection of `H ×_k X`. -/
theorem universalDivisorIso_hom_comp_fst [IsCurve k f] [Smooth f] [IsProper f] {d : ℕ}
    {H H' : Over (Spec (.of k))} (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    (universalDivisorIso f hH hH').hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫
        pullback.fst f H'.hom = (prod.snd : H ⨯ Over.mk f ⟶ Over.mk f).left := by
  let : SmoothOfRelativeDimension 1 (Over.mk f).hom := smoothOfRelativeDimension_one_of_isCurve f
  let : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  exact (comp_subschemeι_comp_eq (universalDivisorIso_hom_comp_subschemeι f hH hH')).2

/-- **Stacks Project, Tag 0B9J, fact (3).** Let `H'` represent `Hilb^{d+1}_{X/k}` and let `p` be
a `k`-rational point of `H'`. Identify `X` with the fibre of `X ×_k H'` over `p` through
`g : X ⟶ X ×_k H'`, and let `D = g⁻¹ D_univ` be the divisor classified by `p`. Then `D` is an
effective Cartier divisor of degree `d + 1` on `X`, and the restriction `g^* 𝒪(D_univ)` of the
invertible sheaf of the universal divisor is `𝒪_X(D)`. -/
theorem nonempty_pullback_invertibleSheaf_universalFamily_iso [IsCurve k f] [Smooth f]
    [IsProper f] {d : ℕ} {H' : Over (Spec (.of k))}
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1))
    (p : Over.mk (𝟙 (Spec (.of k))) ⟶ H') (g : X ⟶ pullback f H'.hom)
    (hgX : g ≫ pullback.fst f H'.hom = 𝟙 X) (hgH : g ≫ pullback.snd f H'.hom = f ≫ p.left) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((hH'.family (𝟙 H')).ideal.comap g) ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          (((hH'.family (𝟙 H')).ideal.comap g).subschemeι ≫ f) (d + 1) ∧
        Nonempty ((Scheme.Modules.pullback g).obj
            (Stacks.Divisors.invertibleSheaf' (hH'.family (𝟙 H')).ideal) ≅
          Stacks.Divisors.invertibleSheaf' ((hH'.family (𝟙 H')).ideal.comap g)) := by
  let : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve f
  let I := (hH'.family (𝟙 H')).ideal
  let P := (Over.pullback (Over.mk (𝟙 (Spec (.of k)))).hom).obj (Over.mk f)
  let e : P.left ≅ X := asIso (pullback.fst f (𝟙 (Spec (.of k))))
  let b := familyBaseChangeMap (Over.mk f) p
  let J := (hH'.family p).ideal
  have hJ : J = I.comap b := by
    simpa only [Category.comp_id] using hH'.naturality p (𝟙 H')
  have hD' : I.comap g = J.comap e.inv := by
    rw [fiber_maps f p g hgX hgH, Scheme.IdealSheafData.comap_comp, ← hJ]
  let m : (J.comap e.inv).subscheme ⟶ J.subscheme :=
    (J.comapIso e.inv).hom ≫ pullback.snd e.inv J.subschemeι
  have hm : m ≫ (J.subschemeι ≫ P.hom) = (J.comap e.inv).subschemeι ≫ f := by
    simp only [m, Category.assoc]
    rw [← pullback.condition_assoc, J.comapIso_hom_fst_assoc,
      show e.inv ≫ P.hom = f by simp [e, P]]
  have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((J.comap e.inv).subschemeι ≫ f) (d + 1) := by
    have hr := Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (asIso m)
      (J.subschemeι ≫ P.hom) (hH'.family p).isFiniteLocallyFreeOfRank
    rwa [asIso_hom, hm] at hr
  let : Stacks.Morphisms.IsFiniteLocallyFree ((J.comap e.inv).subschemeι ≫ f) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ (d + 1) hrank
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap g) := by
    rw [hD']
    exact (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f (J.comap e.inv)).1
  exact ⟨hcart, by rwa [hD'], ⟨@Stacks.Divisors.invertibleSheafPullbackIso _ _ g I
    (isRelativeEffectiveCartierDivisor_universalFamily f hH').1 hcart⟩⟩

end Stacks.Hilbert

end
