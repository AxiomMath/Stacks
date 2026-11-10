module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSeparated
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# Rig-surjectivity of the diagonal of a completed morphism

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a closed set of points of `X`, with `U ⊂ X` the open
subspace with `|U| = |X| ∖ T` and `U' = f⁻¹U ⊂ X'`; this is the situation of **Stacks 0GDB**.
**Stacks 0GDI** says that if `f` is separated and `U' → U` is a monomorphism, then the diagonal
`Δ_{f_{/T}} : X'_{/T'} ⟶ X'_{/T'} ×_{X_{/T}} X'_{/T'}` of the completed morphism is
rig-surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_diagonal_completionSheafMap`: **Stacks 0GDI**.
* `AlgebraicGeometry.Space.isSurjective_fromPreimage_diagonal`: the restriction of `Δ_f` to the
  open complements of `T'` and `T''` is surjective when `U' → U` is a monomorphism.
* `AlgebraicGeometry.FormalSpace.IsRigSurjective.isIso_comp` and
  `AlgebraicGeometry.FormalSpace.IsRigSurjective.comp_isIso`: rig-surjectivity is unchanged by
  composing with an isomorphism on either side.

## Implementation notes

The proof is the source's. By **Stacks 0GDF**, through
`AlgebraicGeometry.Space.pullback_diagonal_completionSheafMap` and
`AlgebraicGeometry.Space.completionSheafDiagonal_eq_completionSheafMap_diagonal`, the diagonal of
`f_{/T}` is the completion `(Δ_f)_{/T''}` of the diagonal `Δ_f : X' ⟶ X' ×_X X'` along the set
`T''` of points of `X' ×_X X'` over `T`, up to isomorphisms on both sides. Since `f` is
separated, `Δ_f` is a closed immersion and so proper (Stacks 04XZ). Over the complement of
`T''` it is the diagonal `U' ⟶ U' ×_U U'`, which is an isomorphism when `U' → U` is a
monomorphism; in particular it is surjective, and **Stacks 0AQW** applies to `Δ_f`.

Surjectivity is checked on sections: a section `(a, b)` of `X' ×_X X'` with all of its points
outside `T''` has `a` and `b` in `U'` with the same image in `U`, so `a = b` because `U' → U`
is a monomorphism, and `(a, b) = Δ_f(a)`.

The source also asks that `X` be locally Noetherian and that `f` be locally of finite type,
which make `X_{/T}` and `X'_{/T'}` locally Noetherian formal algebraic spaces and `f_{/T}`
locally of finite type, so that rig-surjectivity of `Δ_{f_{/T}}` is defined in the source's
sense. The proof does not use either hypothesis, and the statement here is proved without
them, as `AlgebraicGeometry.FormalSpace.isRigSurjective_completionSheafMap` is.

## References

* [Stacks Project, Tag 0GDI](https://stacks.math.columbia.edu/tag/0GDI)
* [Stacks Project, Tag 0GDF](https://stacks.math.columbia.edu/tag/0GDF)
* [Stacks Project, Tag 0AQW](https://stacks.math.columbia.edu/tag/0AQW)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
private instance (priority := high) hasPullbacks_presheaf_CompletionDiagonalRigSurjective :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_CompletionDiagonalRigSurjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CompletionDiagonalRigSurjective (B := B) (S := S) (hS := hS)).has_limit _

namespace Space

/-- If the restriction `U' ⟶ U` of `f : X' ⟶ X` to the open complements of `T` and `|f|⁻¹ T` is
a monomorphism, then the restriction of the diagonal `Δ_f : X' ⟶ X' ×_X X'` to the open
complements of `|f|⁻¹ T` and of the set `T''` of points of `X' ×_X X'` over `T` is surjective:
a section `(a, b)` of `X' ×_X X'` with no point over `T` has `a` and `b` in `U'` with the same
image in `U`, hence `a = b`, and `(a, b) = Δ_f(a)`. -/
theorem isSurjective_fromPreimage_diagonal {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (T : Set (points B S hS X))
    (hmono : Mono ((openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f)) :
    IsSurjective B S hS ((openSubspaceOfPoints B S hS (pullback f f)
      (pullbackPoints B S hS f f T)ᶜ).fromPreimage (pullback.diagonal f)) := by
  let U := openSubspaceOfPoints B S hS X Tᶜ
  let U'' := openSubspaceOfPoints B S hS (pullback f f) (pullbackPoints B S hS f f T)ᶜ
  have hpre₁ : U.preimage (pullback.fst f f ≫ f) = U'' := by
    rw [preimage_openSubspaceOfPoints, Set.preimage_compl]
    rfl
  have hpre₂ : U.preimage (pullback.snd f f ≫ f) = U'' := by
    rw [← pullback.condition, hpre₁]
  have hinj : ∀ K, Function.Injective ((U.fromPreimage f).app K) := fun K =>
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp hmono K)
  have happ : ∀ K, Function.Surjective ((U''.fromPreimage (pullback.diagonal f)).app K) := by
    rintro K ⟨v, hv⟩
    let a := (pullback.fst f f).app K v
    let b := (pullback.snd f f).app K v
    have ha : a ∈ (U.preimage f).obj K :=
      show v ∈ (U.preimage (pullback.fst f f ≫ f)).obj K by rw [hpre₁]; exact hv
    have hb : b ∈ (U.preimage f).obj K :=
      show v ∈ (U.preimage (pullback.snd f f ≫ f)).obj K by rw [hpre₂]; exact hv
    have hfab : f.app K a = f.app K b :=
      congrArg (fun φ => φ.app K v) (pullback.condition (f := f) (g := f))
    have hab : a = b :=
      congrArg Subtype.val (hinj K (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hfab))
    have hv' : (pullback.diagonal f).app K a = v := by
      apply yonedaEquiv.symm.injective
      apply pullback.hom_ext
      · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right,
          ← NatTrans.comp_app_apply, pullback.diagonal_fst]
        rfl
      · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right,
          ← NatTrans.comp_app_apply, pullback.diagonal_snd, hab]
        rfl
    refine ⟨⟨a, show (pullback.diagonal f).app K a ∈ U''.obj K by rw [hv']; exact hv⟩, ?_⟩
    exact Subtype.ext hv'
  intro z
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  obtain ⟨w, hw⟩ := happ (op p.siteObject) p.value
  refine ⟨(⟨p.carrier, p.contained, p.toBase, w⟩ : FieldValuedPoint B S hS _).class B S hS _, ?_⟩
  exact congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
    FieldValuedPoint B S hS U''.toFunctor).class B S hS U''.toFunctor) hw

end Space

namespace FormalSpace

/-- Rig-surjectivity is unchanged by precomposing with an isomorphism: by Stacks 0AQT,
`e ≫ g` is the second factor of `inv e ≫ e ≫ g = g`. -/
theorem IsRigSurjective.isIso_comp {X Y Z : FppfSheaf B S hS} (e : X ⟶ Y) [IsIso e]
    (g : Y ⟶ Z) (hg : IsRigSurjective B S hS g) : IsRigSurjective B S hS (e ≫ g) :=
  IsRigSurjective.of_comp B S hS (inv e) (e ≫ g) (by simpa using hg)

/-- Rig-surjectivity is unchanged by postcomposing with an isomorphism: an adic point of the
new target becomes an adic point of the old one after composing with the inverse, an
isomorphism being representable by algebraic spaces. -/
theorem IsRigSurjective.comp_isIso {X Y Z : FppfSheaf B S hS} (g : X ⟶ Y) (e : Y ⟶ Z)
    [IsIso e] (hg : IsRigSurjective B S hS g) : IsRigSurjective B S hS (g ≫ e) := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  have : IsIso e.hom := Functor.map_isIso (sheafToPresheaf _ _) e
  have hsq : IsPullback (𝟙 _) (p ≫ inv e).hom p.hom e.hom :=
    IsPullback.of_horiz_isIso ⟨by
      change 𝟙 _ ≫ p.hom = ((p ≫ inv e) ≫ e).hom
      rw [Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩
  have hp' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ inv e).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hsq hp
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e', x, he', hx⟩ := hg R hRadic hRcomplete hRweak D (p ≫ inv e) hp'
  refine ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e', x, he', ?_⟩
  rw [← Category.assoc, hx]
  simp

/-- **Stacks 0GDI.** In the situation of Stacks 0GDB, let `f : X' ⟶ X` be a separated morphism
of algebraic spaces over `S`, let `T` be a closed set of points of `X`, and let the restriction
`U' ⟶ U` of `f` to the open complements of `T` and of `T' = |f|⁻¹ T` be a monomorphism. Then
the diagonal `Δ_{f_{/T}} : X'_{/T'} ⟶ X'_{/T'} ×_{X_{/T}} X'_{/T'}` of the completed morphism
is rig-surjective.

By Stacks 0GDF it is the completion of `Δ_f : X' ⟶ X' ×_X X'` along the set of points over
`T`, up to isomorphisms; `Δ_f` is a closed immersion, hence proper, and is surjective over the
complement of `T`, so Stacks 0AQW applies. The source's hypotheses that `X` be locally
Noetherian and `f` locally of finite type are not needed. -/
@[stacks 0GDI]
theorem isRigSurjective_diagonal_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T) (hf : Space.IsSeparated B S hS f)
    (hmono : Mono ((Space.openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f)) :
    IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T)) := by
  have hX'' : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  have hT'' : @IsClosed _ (Space.pointTopology B S hS (pullback f f))
      (Space.pullbackPoints B S hS f f T) :=
    @IsClosed.preimage _ _ (Space.pointTopology B S hS _) (Space.pointTopology B S hS X) _
      (Space.continuous_pointsMap B S hS _) T hT
  have hΔ : IsRigSurjective B S hS (Space.completionSheafMap B S hS (pullback.diagonal f)
      (Space.pullbackPoints B S hS f f T)) :=
    isRigSurjective_completionSheafMap hX' hX'' (pullback.diagonal f) _ hT''
      (Space.isProper_of_isClosedImmersion B S hS hX' hX'' _ hf)
      (Space.isSurjective_fromPreimage_diagonal f T hmono)
  rw [Space.pullback_diagonal_completionSheafMap B S hS f T,
    Space.completionSheafDiagonal_eq_completionSheafMap_diagonal, Category.assoc]
  exact IsRigSurjective.isIso_comp _ _ (IsRigSurjective.comp_isIso _ _ hΔ)

end FormalSpace

end AlgebraicGeometry

end
