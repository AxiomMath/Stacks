module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiAffine

/-!
# Quasi-affine morphisms of algebraic spaces and their local criteria

A morphism of algebraic spaces over a scheme `S` is *quasi-affine* when each of its base
changes along a morphism from an affine object of the big fppf site is represented by an
object of the site whose underlying scheme is quasi-affine; that property is
`AlgebraicGeometry.Space.IsQuasiAffineHom` ([Stacks, Tag 03WL]). This file proves the criteria
of [Stacks, Tag 03WM] which do not need descent along a covering: the property follows from
representability together with quasi-affineness of all represented base changes, it can be
read off a surjective étale scheme chart of the target, and it is stable under base change,
hence holds on the members of a Zariski covering of the target.

## Main results

* `AlgebraicGeometry.Scheme.isQuasiAffine_of_isQuasiAffineHom` and
  `AlgebraicGeometry.isQuasiAffineHom_of_isQuasiAffine`: over an affine target a morphism
  of schemes is quasi-affine exactly when its source is a quasi-affine scheme.
* `AlgebraicGeometry.Space.IsQuasiAffineHom.of_isPullback`: quasi-affineness of a morphism of
  algebraic spaces is stable under arbitrary base change.
* `AlgebraicGeometry.Space.isQuasiAffineHom_of_presheaf`: a representable morphism all of
  whose represented base changes are quasi-affine morphisms of schemes is quasi-affine.
  This is the implication (1) ⇒ (2) of [Stacks, Tag 03WM].
* `AlgebraicGeometry.Space.exists_etaleChart_isQuasiAffineHom_of_presheaf`: such a morphism
  becomes quasi-affine on a surjective étale scheme chart of the target, together with an
  explicit object of the site representing the base change. This is the implication
  (1) ⇒ (3) of [Stacks, Tag 03WM].
* `AlgebraicGeometry.Space.exists_isZariskiCover_isQuasiAffineHom_of_presheaf` and
  `AlgebraicGeometry.Space.exists_isZariskiCover_isQuasiAffineHom`: such a morphism, and
  already a quasi-affine morphism of algebraic spaces, is quasi-affine on the members of a
  Zariski covering of the target. These are the implications (1) ⇒ (4) and (2) ⇒ (4) of
  [Stacks, Tag 03WM].

## Implementation notes

The condition defining `AlgebraicGeometry.Space.IsQuasiAffineHom` asks for the representing
object to have quasi-affine underlying scheme, an absolute condition, rather than for its
projection to the affine test object to be a quasi-affine morphism. The two agree, by
`AlgebraicGeometry.Scheme.isQuasiAffine_of_isQuasiAffineHom` and
`AlgebraicGeometry.isQuasiAffineHom_of_isQuasiAffine`.

## References

* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
* [Stacks Project, Tag 03WO](https://stacks.math.columbia.edu/tag/03WO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme quasi-affine over an affine scheme is a quasi-affine scheme. -/
theorem Scheme.isQuasiAffine_of_isQuasiAffineHom {W Z : Scheme.{u}} (p : W ⟶ Z)
    (hp : IsQuasiAffineHom p) (hZ : IsAffine Z) : Scheme.IsQuasiAffine W := by
  have := hp
  have := hZ
  have h : Scheme.IsQuasiAffine (p ⁻¹ᵁ (⊤ : Z.Opens)).toScheme :=
    IsQuasiAffineHom.isQuasiAffine_preimage ⊤ (isAffineOpen_top Z)
  rw [show (p ⁻¹ᵁ (⊤ : Z.Opens)) = ⊤ from by simp] at h
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  exact Scheme.IsQuasiAffine.of_isImmersion W.topIso.inv

/-- A morphism from a quasi-affine scheme to an affine scheme is quasi-affine. -/
@[ega "II 5.1.1" "special case"]
theorem isQuasiAffineHom_of_isQuasiAffine {W Z : Scheme.{u}} (p : W ⟶ Z)
    (hW : Scheme.IsQuasiAffine W) (hZ : IsAffine Z) : IsQuasiAffineHom p := by
  have := hW
  have := hZ
  have hqc : QuasiCompact p := quasiCompact_of_compactSpace p
  refine ⟨fun U hU ↦ ?_⟩
  have : CompactSpace (p ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp ((quasiCompact_iff_forall_isAffineOpen.mp hqc) U hU)
  exact Scheme.IsQuasiAffine.of_isImmersion (p ⁻¹ᵁ U).ι

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism onto a chosen pullback exhibits its source as a pullback. -/
theorem isPullback_of_iso_pullback {C : Type*} [Category C] {P X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (e : P ≅ pullback f g) :
    IsPullback (e.hom ≫ pullback.fst f g) (e.hom ≫ pullback.snd f g) f g :=
  IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e rfl rfl

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Quasi-affineness of a morphism of algebraic spaces over `S` is stable under base change: if
`f'` sits in a Cartesian square over `f`, then `f'` is quasi-affine as soon as `f` is. -/
@[stacks 03WO]
theorem IsQuasiAffineHom.of_isPullback {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : IsQuasiAffineHom B S hS f) : IsQuasiAffineHom B S hS f' := by
  intro Z h
  obtain ⟨W, hW, ⟨e⟩⟩ := hf Z (h ≫ g)
  exact ⟨W, hW, ⟨(IsPullback.of_right' (isPullback_of_iso_pullback (h ≫ g) f e).flip
    sq).flip.isoPullback⟩⟩

/-- **[Stacks, Tag 03WM], (1) implies (2).** A representable morphism of algebraic spaces over
`S` all of whose represented base changes are quasi-affine morphisms of schemes is quasi-affine.
-/
theorem isQuasiAffineHom_of_presheaf {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsQuasiAffineHom B S hS f := by
  intro Z g
  exact ⟨hf.rep.pullback g, Scheme.isQuasiAffine_of_isQuasiAffineHom _ (hf.property_snd g)
    Z.property, ⟨(hf.rep.isPullback g).flip.isoPullback⟩⟩

/-- **[Stacks, Tag 03WM], (1) implies (3).** A representable morphism of algebraic spaces over
`S` all of whose represented base changes are quasi-affine morphisms of schemes becomes
quasi-affine on a surjective étale scheme chart of the target, with the base change along the
chart represented by an object of the site. -/
theorem exists_etaleChart_isQuasiAffineHom_of_presheaf {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (W : BigFppfOver B S hS)
        (e : yoneda.obj W ≅ pullback g f),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      _root_.AlgebraicGeometry.IsQuasiAffineHom
        ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (e.hom ≫ pullback.fst g f))) := by
  obtain ⟨V, g, hsurj, hetale⟩ := hY.exists_atlas
  refine ⟨V, g, hf.rep.pullback g, (hf.rep.isPullback g).flip.isoPullback,
    hsurj, hetale, ?_⟩
  rw [IsPullback.isoPullback_hom_fst, Functor.preimage_map]
  exact hf.property_snd g

/-- The one-member family consisting of the top subfunctor of an algebraic space over `S` is
a Zariski covering of it. -/
private theorem isZariskiCover_singletonTop (hY : IsAlgebraicSpace B S hS Y) :
    IsZariskiCover B S hS PUnit.{u + 1} (fun _ ↦ (⊤ : Subfunctor Y)) := by
  refine ⟨fun _ ↦ ⟨hY.of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor Y))).symm,
    MorphismProperty.presheaf_of_isIso _ _⟩, ?_⟩
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (Sigma.ι_desc (fun _ : PUnit.{u + 1} ↦ (⊤ : Subfunctor Y).ι) PUnit.unit)

/-- **[Stacks, Tag 03WM], (2) implies (4).** A quasi-affine morphism of algebraic spaces over
`S` is quasi-affine on the members of a Zariski covering of its target. -/
theorem exists_isZariskiCover_isQuasiAffineHom {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsQuasiAffineHom B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_singletonTop hY,
    fun _ ↦ IsQuasiAffineHom.of_isPullback
      (IsPullback.of_hasPullback (⊤ : Subfunctor Y).ι f).flip hf⟩

/-- **[Stacks, Tag 03WM], (1) implies (4).** A representable morphism of algebraic spaces over
`S` all of whose represented base changes are quasi-affine morphisms of schemes is quasi-affine
on the members of a Zariski covering of its target. -/
theorem exists_isZariskiCover_isQuasiAffineHom_of_presheaf {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f) :=
  exists_isZariskiCover_isQuasiAffineHom hY (isQuasiAffineHom_of_presheaf hf)

end Space

end AlgebraicGeometry

end
