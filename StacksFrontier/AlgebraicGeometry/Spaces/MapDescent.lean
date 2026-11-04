module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal

/-!
# The comparison of two fibre products of algebraic spaces

Let `f : X ⟶ Z` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, and let
`h : Z ⟶ T` be a further morphism. The canonical comparison `X ×[Z] Y ⟶ X ×[T] Y` is a
base change of the relative diagonal of `h`, and every property it enjoys is inherited from
that diagonal.

## Main results

* `CategoryTheory.Limits.pullback.mono_mapDesc`: the comparison of fibre products is a
  monomorphism, in any category.
* `CategoryTheory.Limits.pullback.isPullback_diagonal_diag`: the relative diagonal of a
  morphism is a base change of the absolute diagonal of its source, in any category.
* `CategoryTheory.Limits.pullback.diagonal_comp_mapDesc`: the relative diagonal of a composite
  is the relative diagonal of its first factor followed by the comparison, in any category.
* `AlgebraicGeometry.Space.presheaf_of_isPullback`: a property of morphisms obtained by
  `CategoryTheory.MorphismProperty.presheaf` is stable under base change.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_iso`: quasi-compactness of an algebraic
  space over `S` is invariant under isomorphism.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`: quasi-compactness of a morphism of
  algebraic spaces is stable under base change.
* `AlgebraicGeometry.Space.isPullback_mapDesc`: the comparison is a base change of the relative
  diagonal of `h`.
* `AlgebraicGeometry.Space.relativelyRepresentable_mapDesc`: the comparison is
  representable.
* `AlgebraicGeometry.Space.isSeparated_mapDesc`: the comparison is separated.
* `AlgebraicGeometry.Space.isImmersion_mapDesc`,
  `AlgebraicGeometry.Space.isClosedImmersion_mapDesc` and
  `AlgebraicGeometry.Space.isQuasiCompact_mapDesc`: the comparison is an immersion, a closed
  immersion, or quasi-compact as soon as `h` is locally separated, separated, or
  quasi-separated.

## References

* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Limits

variable {C : Type v} [Category.{w} C]

/-- The canonical comparison `X ×[Z] Y ⟶ X ×[T] Y` induced by a morphism `Z ⟶ T` is a
monomorphism. -/
@[stacks 03KN "part (1): monomorphism"]
instance pullback.mono_mapDesc {X Y Z T : C} (f : X ⟶ Z) (g : Y ⟶ Z) (i : Z ⟶ T)
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] :
    Mono (pullback.mapDesc f g i) where
  right_cancellation _ _ huv := pullback.hom_ext
    (by simpa [pullback.lift_fst] using huv =≫ pullback.fst (f ≫ i) (g ≫ i))
    (by simpa [pullback.lift_snd] using huv =≫ pullback.snd (f ≫ i) (g ≫ i))

/-- Two maps into `X ×[Y] X` agreeing after the comparison to `X ⨯ X` are equal. -/
private theorem pullback.hom_ext_of_prod_lift {X Y W : C} {f : X ⟶ Y} [HasPullback f f]
    [HasBinaryProduct X X] {u v : W ⟶ pullback f f}
    (h : u ≫ prod.lift (pullback.fst f f) (pullback.snd f f) =
      v ≫ prod.lift (pullback.fst f f) (pullback.snd f f)) : u = v :=
  pullback.hom_ext (by simpa using h =≫ prod.fst) (by simpa using h =≫ prod.snd)

/-- The relative diagonal of `f : X ⟶ Y` is a base change of the absolute diagonal of `X`
along the canonical map `X ×[Y] X ⟶ X ⨯ X`. -/
theorem pullback.isPullback_diagonal_diag {X Y : C} (f : X ⟶ Y)
    [HasPullback f f] [HasBinaryProduct X X] :
    IsPullback (𝟙 X) (pullback.diagonal f) (diag X)
      (prod.lift (pullback.fst f f) (pullback.snd f f)) := by
  have hd : 𝟙 X ≫ diag X
      = pullback.diagonal f ≫ prod.lift (pullback.fst f f) (pullback.snd f f) := by
    ext <;> simp
  refine ⟨⟨hd⟩, ⟨PullbackCone.IsLimit.mk hd (fun s ↦ s.fst) (fun _ ↦ by simp)
    (fun s ↦ pullback.hom_ext_of_prod_lift (by simpa using s.condition))
    fun _ _ hm₁ _ ↦ by simpa using hm₁⟩⟩

/-- The relative diagonal of a composite `f ≫ g` factors through the relative diagonal of `f`:
the comparison `X ×[Y] X ⟶ X ×[Z] X` of `CategoryTheory.Limits.pullback.mapDesc` carries
`Δ_{X/Y}` to `Δ_{X/Z}`. -/
@[reassoc]
theorem pullback.diagonal_comp_mapDesc {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullback f f] [HasPullback (f ≫ g) (f ≫ g)] :
    pullback.diagonal (f ≫ g) = pullback.diagonal f ≫ pullback.mapDesc f f g :=
  pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst]; simp)
    (by rw [Category.assoc, pullback.lift_snd]; simp)

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Transport along a base change -/

/-- A property of morphisms of algebraic spaces obtained from a property of scheme morphisms
by `CategoryTheory.MorphismProperty.presheaf` is stable under base change. -/
theorem presheaf_of_isPullback {Q : MorphismProperty (BigFppfOver B S hS)}
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'}
    (sq : IsPullback a b p q) (hp : Q.presheaf p) : Q.presheaf b :=
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) Q
  MorphismProperty.of_isPullback sq hp

/-- An isomorphism of presheaves has every property of morphisms of algebraic spaces obtained
by `CategoryTheory.MorphismProperty.presheaf` from a property of scheme morphisms which
respects isomorphisms and holds for the identities. -/
theorem presheaf_of_isIso {Q : MorphismProperty (BigFppfOver B S hS)} (hQi : Q.RespectsIso)
    (hQ : ∀ U : BigFppfOver B S hS, Q (𝟙 U))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] : Q.presheaf e := by
  have := hQi
  have hid : Q.presheaf (𝟙 F) := MorphismProperty.relative.of_exists
    (fun _ g ↦ ⟨_, g, 𝟙 _, by simpa using IsPullback.of_id_snd, hQ _⟩)
  simpa using MorphismProperty.RespectsIso.postcomp _ e (𝟙 F) hid

/-- Quasi-compactness of an algebraic space is invariant under isomorphism. -/
theorem isQuasiCompactSpace_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : IsQuasiCompactSpace B S hS F) : IsQuasiCompactSpace B S hS G := by
  obtain ⟨U, a, hcompact, hsurj, hetale⟩ := hF
  refine ⟨U, a ≫ e.hom, hcompact, MorphismProperty.RespectsIso.postcomp _ e.hom a hsurj, ?_⟩
  intro V φ hφ
  simpa using MorphismProperty.RespectsIso.postcomp _ e.hom _ (hetale V φ hφ)

/-- Quasi-compactness of a morphism of algebraic spaces is stable under base change: in a
cartesian square, the base change `b` of a quasi-compact `p` is quasi-compact. -/
@[stacks 03HF]
theorem isQuasiCompact_of_isPullback {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'}
    (sq : IsPullback a b p q) (hp : IsQuasiCompact B S hS p) : IsQuasiCompact B S hS b :=
  fun W hW hWqc w ↦ isQuasiCompactSpace_of_iso B S hS
    ((IsPullback.of_hasPullback w b).paste_vert sq.flip).isoPullback.symm (hp W hW hWqc (w ≫ q))

/-! ### The two squares -/

/-- The comparison `Z ×[T] Z ⟶ Z ⨯ Z` of the fibre product of `h : Z ⟶ T` with itself and the
product is a monomorphism. -/
theorem mono_prodLift_pullback (h : Z ⟶ T) :
    Mono (prod.lift (pullback.fst h h) (pullback.snd h h)) :=
  ⟨fun _ _ huv ↦ pullback.hom_ext_of_prod_lift huv⟩

/-- The *magic diagram*: the comparison `X ×[Z] Y ⟶ X ×[T] Y` is a base change of the
relative diagonal of `h : Z ⟶ T`. -/
theorem isPullback_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    IsPullback (pullback.fst f g ≫ f) (pullback.mapDesc f g h) (pullback.diagonal h)
      (pullback.map (f ≫ h) (g ≫ h) h h f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) :=
  pullback_map_diagonal_isPullback f g h

/-! ### The properties of the comparison -/

/-- The comparison of fibre products is representable. -/
@[stacks 03KN "part (1): representable"]
theorem relativelyRepresentable_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) :=
  MorphismProperty.of_isPullback (isPullback_mapDesc B S hS f g h)
    (MorphismProperty.of_isPullback (isPullback_pullbackDiagonal_diag B S hS h)
      hZ.diagonal_representable)

/-- The comparison of fibre products is separated. -/
@[stacks 03KN "part (1): separated"]
theorem isSeparated_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    IsSeparated B S hS (pullback.mapDesc f g h) :=
  presheaf_of_isIso B S hS (MorphismProperty.RespectsIso.inverseImage _ _)
    (fun U ↦ show _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (𝟙 U)) by
        rw [CategoryTheory.Functor.map_id]; infer_instance) _

/-- The comparison of fibre products is an immersion when `h : Z ⟶ T` is locally separated. -/
@[stacks 03KN "part (2)", ega "I 5.3.10"]
theorem isImmersion_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hh : IsLocallySeparated B S hS h) :
    IsImmersion B S hS (pullback.mapDesc f g h) :=
  presheaf_of_isPullback B S hS (isPullback_mapDesc B S hS f g h) hh

/-- The comparison of fibre products is a closed immersion when `h : Z ⟶ T` is separated. -/
@[stacks 03KN "part (3)", ega "I 5.4.2"]
theorem isClosedImmersion_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hh : IsSeparated B S hS h) :
    IsClosedImmersion B S hS (pullback.mapDesc f g h) :=
  presheaf_of_isPullback B S hS (isPullback_mapDesc B S hS f g h) hh

/-- The comparison of fibre products is quasi-compact when `h : Z ⟶ T` is quasi-separated. -/
@[stacks 03KN "part (4)"]
theorem isQuasiCompact_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hh : IsQuasiSeparated B S hS h) :
    IsQuasiCompact B S hS (pullback.mapDesc f g h) :=
  isQuasiCompact_of_isPullback B S hS (isPullback_mapDesc B S hS f g h) hh

end AlgebraicGeometry.Space

end
