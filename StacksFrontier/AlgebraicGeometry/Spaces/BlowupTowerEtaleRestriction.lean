module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupOfEffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Restricting a sequence of blowings up at closed points to an étale neighborhood

Let `S` be a scheme, let `X` be a decent algebraic space over `S`, let `x₁, …, xₙ ∈ |X|` be
pairwise distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the elementary étale
neighborhoods chosen in Stacks 0BH9, that is a term `D : ClosedPointNeighborhoods B S hS n`.
If `f : Y ⟶ X` factors as a sequence

`Y = Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

of blowings up at closed points lying over `{x₁, …, xₙ}`, then for every `i` the base change
`gᵢ : Yᵢ ⟶ Uᵢ` of `f` along `Uᵢ ⟶ X` factors as a sequence

`Yᵢ = Z_{i, mᵢ} ⟶ … ⟶ Z_{i, 1} ⟶ Z_{i, 0} = Uᵢ`

of blowings up at closed points lying over `uᵢ`.  This is the **"only if" direction of
Stacks 0BHF**; for the converse see the implementation notes.

The sequence over `Uᵢ` is the base change of the given one: `Z_{i, j} = Z_j ×_X Uᵢ`.  Each step
is a blowing up by Stacks 085S, blowing up commuting with the flat — indeed étale — base change
`Z_{i, j} ⟶ Z_j`; what has to be seen is that the centre of the base-changed step is again the
reduced closed subspace on a *single* closed point, lying over `uᵢ`.

## Main results

* `CategoryTheory.Subfunctor.isIso_fromPreimage_of_le_preimage`: if a morphism carries the
  inverse image of a subfunctor `T` isomorphically onto `T`, then so does any base change of it,
  over any subfunctor of the new base contained in the inverse image of `T`.
* `AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isBlowupAtClosedPoint`: Stacks 085S for a
  morphism which *is* the blowing up at a closed point.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_preimage_closedPointSubspace`: the
  inverse image, in `Z ×_X Uᵢ`, of the reduced closed subspace on a closed point of `Z` lying
  over `xᵢ` is the reduced closed subspace on a single closed point, and that point lies
  over `uᵢ`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isEmpty_points_preimage_closedPointSubspace`:
  the same inverse image has no points at all when the closed point lies over `x_j` for
  `j ≠ i`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_of_isPullback`: the base
  change along `Uᵢ ⟶ X` of a tower of blowings up at closed points over `{x₁, …, xₙ}` is a tower
  of blowings up at closed points over `uᵢ`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_localBlowupFactorization`: **the
  "only if" direction of Stacks 0BHF** for an arbitrary base change of `f`, and
  `…nonempty_localBlowupFactorization_restrictionComponent`: the same for the base change given
  by the functor `F` of Stacks 0BHA.

## Implementation notes

### Why the centre of the base-changed blowing up is again a point

Write `π : Uᵢ ⟶ X` and let `p : P ⟶ Z`, `q : P ⟶ Uᵢ` exhibit `P = Z ×_X Uᵢ`.  Let `z ∈ |Z|` be
a closed point lying over `xᵢ` and let `C ⊆ Z` be the reduced closed subspace on `{z}`, the
centre of Stacks 0BHE.  The inverse image `C ×_Z P` is a closed subspace of `P`; it is
étale-locally reduced because its projection to `C` is a base change of the étale `p`; and the
whole point is that this projection is an **isomorphism**, so that the inverse image has exactly
one point.  By the uniqueness half of Stacks 03IQ it is then the reduced closed subspace on that
point.

The projection is an isomorphism because the corresponding projection is one one level down: the
étale morphism `π` carries the inverse image of the subspace `{xᵢ} ⊆ X` isomorphically onto it,
which is `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_fromPreimage_pointSubspace` —
the second standing hypothesis of Stacks 0BGY at `(Uᵢ ⟶ X, {xᵢ})`, and the formal content of
the source's "`uᵢ ⟶ xᵢ` is an isomorphism".  Being an isomorphism is inherited by base change,
and `C` lies inside the inverse image of `{xᵢ}` because `C` is reduced with image point `xᵢ`,
so Stacks 03JJ factors it through that closed subspace.  The passage from `{xᵢ}` to `C` is
`CategoryTheory.Subfunctor.isIso_fromPreimage_of_le_preimage`.

For a centre lying over `x_j` with `j ≠ i` no point of `Uᵢ` lies over `x_j`, by the shrinking
condition of Stacks 0BH9, so the inverse image of the centre has no points; it is then an
effective Cartier divisor and the base-changed blowing up is an isomorphism by Stacks 085V.
The tower is left unchanged at that step, transported along the isomorphism.

### The converse

The converse direction of Stacks 0BHF, that local factorizations of every `gᵢ` give a global
factorization of `f`, is `nonempty_globalBlowupFactorization_of_isPullback` in the namespace
`AlgebraicGeometry.Space.ClosedPointNeighborhoods`, with its specialization
`nonempty_globalBlowupFactorization_restrictionComponent` at the functor `F` of Stacks 0BHA;
the two directions together are `nonempty_globalBlowupFactorization_iff`, which carries the
`@[stacks 0BHF]` attribute.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BHD](https://stacks.math.columbia.edu/tag/0BHD)
* [Stacks Project, Tag 0BHG](https://stacks.math.columbia.edu/tag/0BHG)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085V](https://stacks.math.columbia.edu/tag/085V)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- **Being carried isomorphically onto a subfunctor is inherited by base change.**  Let

```
P ⟶ V
↓    ↓
W ⟶ X
```

be a cartesian square of presheaves of types, let `T ⊆ X` be a subfunctor whose inverse image in
`V` is carried isomorphically onto `T` by `V ⟶ X`, and let `Z ⊆ W` be a subfunctor contained in
the inverse image of `T`.  Then the inverse image of `Z` in `P` is carried isomorphically onto
`Z` by `P ⟶ W`.

The inverse image of `Z` in `P` is `Z ×_W P = Z ×_X V = Z ×_T (T ×_X V)`, and `T ×_X V ⟶ T` is
the given isomorphism. -/
theorem isIso_fromPreimage_of_le_preimage {𝒞 : Type*} [Category 𝒞] {X V W P : 𝒞 ⥤ Type u}
    {π : V ⟶ X} {g : W ⟶ X} {p : P ⟶ W} {q : P ⟶ V} (sq : IsPullback p q g π)
    (T : Subfunctor X) (hT : IsIso (T.fromPreimage π))
    (Z : Subfunctor W) (hZ : Z ≤ T.preimage g) :
    IsIso (Z.fromPreimage p) := by
  have hr : Subfunctor.range Z.ι ≤ T.preimage g := by rwa [Subfunctor.range_ι]
  have hk : Subfunctor.lift Z.ι hr ≫ (T.preimage g).ι = Z.ι := Subfunctor.lift_ι _ _
  have hc : (Subfunctor.lift Z.ι hr ≫ T.fromPreimage g) ≫ T.ι = Z.ι ≫ g := by
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hk]
  have s1 := Subfunctor.isPullback_preimage p Z
  have s3 := Subfunctor.isPullback_preimage π T
  have s12 := s1.paste_vert sq
  have hcompat : (Z.fromPreimage p ≫ Subfunctor.lift Z.ι hr ≫ T.fromPreimage g) ≫ T.ι =
      ((Z.preimage p).ι ≫ q) ≫ π := by
    rw [Category.assoc, hc, ← Category.assoc, Subfunctor.fromPreimage_ι]
    simp only [Category.assoc, sq.w]
  have ha1 : s3.lift _ _ hcompat ≫ T.fromPreimage π =
      Z.fromPreimage p ≫ Subfunctor.lift Z.ι hr ≫ T.fromPreimage g := s3.lift_fst _ _ hcompat
  have ha2 : s3.lift _ _ hcompat ≫ (T.preimage π).ι = (Z.preimage p).ι ≫ q :=
    s3.lift_snd _ _ hcompat
  have sfinal : IsPullback (Z.fromPreimage p) (s3.lift _ _ hcompat)
      (Subfunctor.lift Z.ι hr ≫ T.fromPreimage g) (T.fromPreimage π) := by
    refine IsPullback.of_bot ?_ ha1.symm s3
    rwa [ha2, hc]
  exact sfinal.flip.isIso_snd_of_isIso hT

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The base change of a blowing up at a closed point -/

/-- Replacing the bottom map `b` of a cartesian square by `b₂` with `e.hom ≫ b₂ = b` for an
isomorphism `e` replaces the second projection `s` by `s ≫ e.hom`. -/
private theorem isPullback_comp_hom_of_comp_eq {C : Type*} [Category C] {W P Y Y₂ X : C}
    {g : W ⟶ X} {r : P ⟶ W} {s : P ⟶ Y} {b : Y ⟶ X} {b₂ : Y₂ ⟶ X} (e : Y ≅ Y₂)
    (he : e.hom ≫ b₂ = b) (sq : IsPullback r s g b) : IsPullback r (s ≫ e.hom) g b₂ := by
  have hiso : IsPullback e.hom b b₂ (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, he]⟩
  have h := sq.flip.paste_horiz hiso
  rw [Category.comp_id] at h
  exact h.flip

/-- The base change along a flat morphism of a morphism which **is** the blowing up at a closed
point `z` is the blowing up in the inverse image of the reduced closed subspace on `{z}`.

This is Stacks 085S, `AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat`,
with the isomorphism carried in `AlgebraicGeometry.Space.IsBlowupAtClosedPoint` absorbed into
the cartesian square. -/
theorem isBlowupAlong_preimage_of_isBlowupAtClosedPoint {X Y W P : AlgebraicSpaces B S hS}
    {g : W ⟶ X} (hg : IsFlat B S hS g.hom) {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {b : Y ⟶ X}
    (hb : IsBlowupAtClosedPoint B S hS z hz b) {r : P ⟶ W} {s : P ⟶ Y}
    (sq : IsPullback r s g b) :
    IsBlowupAlong B S hS (preimageClosedSubspace g (closedPointSubspace B S hS z hz)) r := by
  obtain ⟨W', b₂, hb₂, e, he⟩ := hb
  exact isBlowupAlong_preimage_of_isPullback_of_isFlat hg hb₂
    (isPullback_comp_hom_of_comp_eq e he sq)

/-! ### Points of the inverse image of the centre -/

/-- A point of the reduced closed subspace on a single closed point of an algebraic space maps to
that point. -/
theorem pointsMap_ι_reducedClosedSubspace_singleton {X : AlgebraicSpaces B S hS}
    (z : points B S hS X.obj) (hz : IsClosed ({z} : Set (points B S hS X.obj)))
    (c : points B S hS (reducedClosedSubspace B S hS X.obj X.property {z} hz).toFunctor) :
    pointsMap B S hS _ (reducedClosedSubspace B S hS X.obj X.property {z} hz).ι c = z := by
  have hm : pointsMap B S hS _ (reducedClosedSubspace B S hS X.obj X.property {z} hz).ι c ∈
      Set.range (pointsMap B S hS _
        (reducedClosedSubspace B S hS X.obj X.property {z} hz).ι) := ⟨c, rfl⟩
  rw [range_pointsMap_ι_reducedClosedSubspace] at hm
  simpa using hm

/-- A point of the inverse image, along `p : P ⟶ Z`, of the reduced closed subspace on a closed
point `z` of `Z` maps to `z`. -/
theorem pointsMap_preimage_closedPointSubspace {Z P : AlgebraicSpaces B S hS}
    {z : points B S hS Z.obj} {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {p : P ⟶ Z}
    (y : points B S hS ((closedPointSubspace B S hS z hz).1.preimage p.hom).toFunctor) :
    pointsMap B S hS P.obj p.hom
        (pointsMap B S hS _ ((closedPointSubspace B S hS z hz).1.preimage p.hom).ι y) = z := by
  have h := congrArg (fun k => pointsMap B S hS _ k y)
    (Subfunctor.fromPreimage_ι (closedPointSubspace B S hS z hz).1 p.hom)
  simp only [pointsMap_comp_apply] at h
  rw [← h]
  exact pointsMap_ι_reducedClosedSubspace_singleton z hz _

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The morphism `Uᵢ ⟶ X` from a chosen elementary étale neighborhood is étale as a morphism of
algebraic spaces over the base. -/
theorem isEtale_toSpaceHom (i : Fin n) : IsEtale B S hS (D.toSpaceHom i).hom :=
  (D.neighborhood i).etale_toSpace

/-- A point of the inverse image, along `p : P ⟶ Z`, of the reduced closed subspace on a closed
point `z` of `Z` over `Uᵢ ⟶ X` maps to the image of `z` in `X`. -/
private theorem pointsMap_toSpaceHom_preimage_closedPointSubspace {Z P : AlgebraicSpaces B S hS}
    {i : Fin n} {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))}
    (y : points B S hS ((closedPointSubspace B S hS z hz).1.preimage p.hom).toFunctor) :
    pointsMap B S hS _ (D.toSpaceHom i).hom (pointsMap B S hS P.obj q.hom
      (pointsMap B S hS _ ((closedPointSubspace B S hS z hz).1.preimage p.hom).ι y)) =
        pointsMap B S hS Z.obj g.hom z := by
  have hwhom : p.hom ≫ g.hom = q.hom ≫ (D.toSpaceHom i).hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      sq.w]
  rw [← pointsMap_apply_comm B S hS hwhom, pointsMap_preimage_closedPointSubspace y]

/-- **No point of the `i`th neighborhood lies over a centre above `x_j` for `j ≠ i`.**  The
inverse image, in `Z ×_X Uᵢ`, of the reduced closed subspace on a closed point of `Z` lying over
`x_j` with `j ≠ i` has no points. -/
theorem isEmpty_points_preimage_closedPointSubspace {Z P : AlgebraicSpaces B S hS} {i j : Fin n}
    (hij : i ≠ j) {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))}
    (hzj : pointsMap B S hS Z.obj g.hom z = D.point j) :
    IsEmpty (points B S hS
      ((closedPointSubspace B S hS z hz).1.preimage p.hom).toFunctor) := by
  refine ⟨fun y => ?_⟩
  exact D.map_ne_point i j hij _
    ((D.pointsMap_toSpaceHom_preimage_closedPointSubspace sq y).trans hzj)

/-- **The centre of the base-changed blowing up is again a closed point, lying over `uᵢ`.**
Let `p : P ⟶ Z`, `q : P ⟶ Uᵢ` exhibit `P = Z ×_X Uᵢ` and let `z` be a closed point of `Z` lying
over the chosen point `xᵢ`.  Then the inverse image in `P` of the reduced closed subspace on
`{z}` is the reduced closed subspace on a single closed point of `P`, and that point lies
over `uᵢ`.

The inverse image is a closed subspace, is étale-locally reduced because its projection to the
reduced closed subspace on `{z}` is a base change of the étale `p`, and has exactly one point
because that projection is an isomorphism: the subspace `{z}` lies inside the inverse image of
the subspace `{xᵢ}` by Stacks 03JJ, and `Uᵢ ⟶ X` carries the inverse image of `{xᵢ}`
isomorphically onto it.  The uniqueness half of Stacks 03IQ then identifies it. -/
theorem exists_preimage_closedPointSubspace {Z P : AlgebraicSpaces B S hS} {i : Fin n}
    {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS Z.obj}
    (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hzi : pointsMap B S hS Z.obj g.hom z = D.point i) :
    ∃ (w : points B S hS P.obj) (hw : IsClosed ({w} : Set (points B S hS P.obj))),
      pointsMap B S hS P.obj q.hom w = D.neighborhoodPoint i ∧
        (closedPointSubspace B S hS z hz).1.preimage p.hom =
          (closedPointSubspace B S hS w hw).1 := by
  classical
  have hCred : HasEtaleLocalProperty B S hS
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Z.obj Z.property {z} hz
  have hCalg : IsAlgebraicSpace B S hS
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS Z.obj Z.property {z} hz
  have hCcl : IsClosedSubspace B S hS (reducedClosedSubspace B S hS Z.obj Z.property {z} hz) :=
    isClosedSubspace_reducedClosedSubspace B S hS Z.obj Z.property {z} hz
  have hmonoC : Mono (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι :=
    mono_of_isClosedImmersion B S hS _ hCcl.2
  have hsub : Set.range (pointsMap B S hS _
        ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι ≫ g.hom)) ⊆
      Set.range (pointsMap B S hS (D.pointSubspace i).toFunctor (D.pointSubspace i).ι) := by
    rw [D.range_pointsMap_ι_pointSubspace i]
    rintro y ⟨c, rfl⟩
    rw [pointsMap_comp_apply, pointsMap_ι_reducedClosedSubspace_singleton z hz c, hzi]
    rfl
  obtain ⟨m, hm⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    D.space.property hCalg (D.pointSubspace i) (D.isClosedSubspace_pointSubspace i) hCred
    ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι ≫ g.hom)).2 hsub
  have hlift : (Subfunctor.isPullback_preimage g.hom (D.pointSubspace i)).lift m
        (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι hm ≫
      ((D.pointSubspace i).preimage g.hom).ι =
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι :=
    (Subfunctor.isPullback_preimage g.hom (D.pointSubspace i)).lift_snd m _ hm
  have hle : reducedClosedSubspace B S hS Z.obj Z.property {z} hz ≤
      (D.pointSubspace i).preimage g.hom := by
    have h := Subfunctor.range_comp_le
      ((Subfunctor.isPullback_preimage g.hom (D.pointSubspace i)).lift m
        (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι hm)
      ((D.pointSubspace i).preimage g.hom).ι
    rwa [hlift, Subfunctor.range_ι, Subfunctor.range_ι] at h
  have hIso : IsIso ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).fromPreimage
      p.hom) :=
    Subfunctor.isIso_fromPreimage_of_le_preimage (AlgebraicSpaces.isPullback_hom B S hS sq)
      (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i) _ hle
  have hAcl : IsClosedSubspace B S hS
      ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).preimage p.hom) :=
    isClosedSubspace_preimage B S hS p.hom _ Z.property P.property hCcl
  have hmonoA : Mono ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).preimage p.hom).ι :=
    mono_of_isClosedImmersion B S hS _ hAcl.2
  have hbij : Function.Bijective (pointsMap B S hS _
      ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).fromPreimage p.hom)) := by
    refine ⟨fun a a' haa' => ?_, fun c => ?_⟩
    · have h := congrArg (pointsMap B S hS _
        (inv ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).fromPreimage p.hom))) haa'
      rwa [← pointsMap_comp_apply, ← pointsMap_comp_apply, IsIso.hom_inv_id, pointsMap_id,
        id_eq, id_eq] at h
    · refine ⟨pointsMap B S hS _
        (inv ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).fromPreimage p.hom)) c, ?_⟩
      rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  have hCsub : ∀ c c' : points B S hS
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).toFunctor, c = c' := by
    intro c c'
    refine pointsMap_injective_of_mono B S hS
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι ?_
    rw [pointsMap_ι_reducedClosedSubspace_singleton z hz c,
      pointsMap_ι_reducedClosedSubspace_singleton z hz c']
  obtain ⟨c₀⟩ : Nonempty (points B S hS
      (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).toFunctor) := by
    have hmem : z ∈ Set.range (pointsMap B S hS _
        (reducedClosedSubspace B S hS Z.obj Z.property {z} hz).ι) := by
      rw [range_pointsMap_ι_reducedClosedSubspace]; rfl
    exact ⟨hmem.choose⟩
  obtain ⟨a₀, -⟩ := hbij.2 c₀
  have hrange : Set.range (pointsMap B S hS _
        ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).preimage p.hom).ι) =
      {pointsMap B S hS _
        ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).preimage p.hom).ι a₀} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨a₀, rfl⟩, ?_⟩
    rintro y ⟨a, rfl⟩
    exact congrArg _ (hbij.1 (hCsub _ _))
  have hwclosed : IsClosed ({pointsMap B S hS _
      ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).preimage p.hom).ι a₀} :
      Set (points B S hS P.obj)) := by
    rw [← hrange]
    exact isClosed_range_pointsMap_of_isClosedImmersion B S hS P.property _ hAcl.2
  refine ⟨_, hwclosed, ?_, ?_⟩
  · exact D.eq_of_map_eq_point i _
      ((D.pointsMap_toSpaceHom_preimage_closedPointSubspace sq a₀).trans hzi)
  · refine eq_closedPointSubspace B S hS _ hwclosed _ hAcl hrange ?_
    exact hasEtaleLocalProperty_of_isEtale B S hS hAcl.1 hCalg
      (isEtale_of_isIso B S hS
        ((reducedClosedSubspace B S hS Z.obj Z.property {z} hz).fromPreimage p.hom)) hCred

/-! ### The base change of a tower of blowings up -/

/-- **The base change along `Uᵢ ⟶ X` of a tower of blowings up at closed points over
`{x₁, …, xₙ}` is a tower of blowings up at closed points over `uᵢ`.**

For a tower with top `Z`, a cartesian square exhibiting `P = Z ×_X Uᵢ` over the structure
morphism `Z ⟶ X` of the tower, the conclusion is a tower over `Uᵢ` with top `P` whose structure
morphism is the given `P ⟶ Uᵢ`.

The induction is on the tower.  At a step blowing up a closed point lying over `xᵢ`, the base
change of that step is the blowing up of `Z_j ×_X Uᵢ` at the closed point produced by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_preimage_closedPointSubspace`, by
Stacks 085S.  At a step blowing up a closed point lying over `x_j` with `j ≠ i`, the inverse
image of the centre has no points, so the base change of that step is an isomorphism by
Stacks 085V and the tower constructed so far is merely transported along it. -/
theorem exists_blowupTower_of_isPullback (i : Fin n) :
    ∀ {Z : AlgebraicSpaces B S hS} (t : BlowupTower B S hS D.space Z),
      t.CentersOver (Set.range D.point) →
      ∀ {P : AlgebraicSpaces B S hS} (p : P ⟶ Z) (q : P ⟶ D.neighborhoodSpace i),
        IsPullback p q t.proj (D.toSpaceHom i) →
        ∃ s : BlowupTower B S hS (D.neighborhoodSpace i) P,
          s.CentersOver ({D.neighborhoodPoint i} : Set (points B S hS _)) ∧ s.proj = q := by
  intro Z t
  induction t with
  | base e =>
      intro _ P p q sq
      have : IsIso q := sq.isIso_snd_of_isIso (by rw [BlowupTower.proj_base]; infer_instance)
      exact ⟨.base (asIso q), trivial, rfl⟩
  | @step Zlow Ztop t b z hz hb ih =>
      intro hcent P p q sq
      rw [BlowupTower.centersOver_step] at hcent
      obtain ⟨s', hs'cent, hs'proj⟩ := ih hcent.1 (pullback.fst t.proj (D.toSpaceHom i))
        (pullback.snd t.proj (D.toSpaceHom i)) (IsPullback.of_hasPullback _ _)
      have sq' : IsPullback (pullback.fst t.proj (D.toSpaceHom i))
          (pullback.snd t.proj (D.toSpaceHom i)) t.proj (D.toSpaceHom i) :=
        IsPullback.of_hasPullback _ _
      have hwsq : (p ≫ b) ≫ t.proj = q ≫ D.toSpaceHom i := by
        rw [Category.assoc]; exact sq.w
      have hr1 : sq'.lift (p ≫ b) q hwsq ≫ pullback.fst t.proj (D.toSpaceHom i) = p ≫ b :=
        sq'.lift_fst _ _ hwsq
      have hr2 : sq'.lift (p ≫ b) q hwsq ≫ pullback.snd t.proj (D.toSpaceHom i) = q :=
        sq'.lift_snd _ _ hwsq
      have sqr : IsPullback (sq'.lift (p ≫ b) q hwsq) p
          (pullback.fst t.proj (D.toSpaceHom i)) b := by
        refine (IsPullback.of_bot ?_ hr1.symm sq').flip
        rwa [hr2]
      have hp'etale : IsEtale B S hS (pullback.fst t.proj (D.toSpaceHom i)).hom :=
        isEtale_of_isPullback B S hS (pullback.snd t.proj (D.toSpaceHom i))
          (pullback.fst t.proj (D.toSpaceHom i)) (D.toSpaceHom i) t.proj sq'.flip
          (D.isEtale_toSpaceHom i)
      have hblow := isBlowupAlong_preimage_of_isBlowupAtClosedPoint
        (isFlat_of_isEtale B S hS hp'etale) hb sqr
      obtain ⟨j, hj⟩ := hcent.2
      rcases eq_or_ne i j with rfl | hij
      · obtain ⟨w, hw, hwq, hwpre⟩ := D.exists_preimage_closedPointSubspace sq' hz hj.symm
        have hbr : IsBlowupAtClosedPoint B S hS w hw (sq'.lift (p ≫ b) q hwsq) := by
          refine isBlowupAtClosedPoint_of_isBlowupAlong ?_
          have he : preimageClosedSubspace (pullback.fst t.proj (D.toSpaceHom i))
              (closedPointSubspace B S hS z hz) = closedPointSubspace B S hS w hw :=
            Subtype.ext hwpre
          rwa [← he]
        refine ⟨.step s' (sq'.lift (p ≫ b) q hwsq) w hw hbr, ?_, ?_⟩
        · rw [BlowupTower.centersOver_step]
          refine ⟨hs'cent, ?_⟩
          rw [hs'proj, hwq]
          rfl
        · rw [BlowupTower.proj_step, hs'proj, hr2]
      · have hempty := D.isEmpty_points_preimage_closedPointSubspace hij sq' (hz := hz) hj.symm
        have : IsIso (sq'.lift (p ≫ b) q hwsq) :=
          hblow.isIso_of_isEffectiveCartierDivisor
            (isEffectiveCartierDivisor_of_isEmpty_points B S hS _ _ hempty)
        refine ⟨s'.comap (asIso (sq'.lift (p ≫ b) q hwsq)), ?_, ?_⟩
        · rwa [BlowupTower.centersOver_comap]
        · rwa [BlowupTower.proj_comap, hs'proj]

/-! ### The "only if" direction of Stacks 0BHF -/

/-- **Stacks 0BHF, the "only if" direction.**  Let `X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BH9 and
let `f : Y ⟶ X` be a morphism of algebraic spaces with base change `gᵢ : Yᵢ ⟶ Uᵢ` along
`Uᵢ ⟶ X`.  If `f` factors as a finite sequence of blowings up at closed points lying over
`{x₁, …, xₙ}`, then `gᵢ` factors as a finite sequence of blowings up at closed points lying
over `uᵢ`.

The sequence over `Uᵢ` is the base change of the given one, which is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_of_isPullback`.  No
hypothesis on `f` beyond the cartesian square is used; in particular `f` need not be an
isomorphism over `X ∖ {x₁, …, xₙ}`, so the statement is stronger than the source's, which fixes
`f` in `C_{X, {x₁, …, xₙ}}`. -/
@[stacks 0BHF "the only-if direction: a factorization of f as a sequence of blowings up at
closed points lying over x₁, …, xₙ gives, for each i, a factorization of its base change gᵢ as a
sequence of blowings up at closed points lying over uᵢ. The if direction is
AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_of_isPullback
and the equivalence itself is
AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_iff."]
theorem nonempty_localBlowupFactorization {i : Fin n} {Y Y' : AlgebraicSpaces B S hS}
    {f : Y ⟶ D.space} {a : Y' ⟶ Y} {g : Y' ⟶ D.neighborhoodSpace i}
    (sq : IsPullback a g f (D.toSpaceHom i)) (F : D.GlobalBlowupFactorization f) :
    Nonempty (D.LocalBlowupFactorization i g) := by
  obtain ⟨s, hscent, hsproj⟩ := D.exists_blowupTower_of_isPullback i F.tower F.centersOver
    (a ≫ F.iso.hom) g (isPullback_comp_hom_of_comp_eq F.iso F.iso_proj sq.flip).flip
  exact ⟨{ top := Y'
           tower := s
           centersOver := hscent
           iso := Iso.refl Y'
           iso_proj := by rw [Iso.refl_hom, Category.id_comp, hsproj] }⟩

/-- **Stacks 0BHF, the "only if" direction, for the functor `F` of Stacks 0BHA.**  Let
`X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BH9 and let `f : Y ⟶ X` be an object of
`C_{X, {x₁, …, xₙ}}` corresponding to `gᵢ : Yᵢ ⟶ Uᵢ` under `F`.  If `f` factors as a finite
sequence of blowings up at closed points lying over `{x₁, …, xₙ}`, then for every `i` the
morphism `gᵢ` factors as a finite sequence of blowings up at closed points lying over `uᵢ`.

This is `AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_localBlowupFactorization` at
the cartesian square of
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isPullback_restrictionComponent_obj`, which is
what "corresponds under `F`" means. -/
@[stacks 0BHF "the only-if direction at the functor F: a factorization of f as a sequence of
blowings up at closed points lying over x₁, …, xₙ gives, for each i, a factorization of
gᵢ = F(f)ᵢ as a sequence of blowings up at closed points lying over uᵢ. The if direction at F
is nonempty_globalBlowupFactorization_restrictionComponent and the equivalence itself is
AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_iff."]
theorem nonempty_localBlowupFactorization_restrictionComponent
    (M : D.modificationsAwayFromPoints) (i : Fin n)
    (F : D.GlobalBlowupFactorization (ObjectProperty.homMk M.obj.hom :
      (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) :
    Nonempty (D.LocalBlowupFactorization i (ObjectProperty.homMk
      ((D.restrictionComponent i).obj M).obj.hom :
      (⟨((D.restrictionComponent i).obj M).obj.left,
          ((D.restrictionComponent i).obj M).property.1⟩ : AlgebraicSpaces B S hS) ⟶
        D.neighborhoodSpace i)) := by
  refine D.nonempty_localBlowupFactorization (a := ObjectProperty.homMk
    (pullback.fst M.obj.hom (D.toSpaceHom i).hom)) ?_ F
  exact IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
    (IsPullback.of_hasPullback M.obj.hom (D.toSpaceHom i).hom)

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
