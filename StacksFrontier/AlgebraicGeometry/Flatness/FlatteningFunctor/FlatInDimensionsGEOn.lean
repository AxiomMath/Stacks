module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatnessTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension

/-!
# Flatness in dimensions at least `n` over a subset of the base

Let `f : X ⟶ S` be a morphism of schemes, `F` an `𝒪_X`-module, `n` a natural number and `W` a
subset of `S`. We say that `F` is flat over `S` in dimensions `≥ n` over `W` when every point `x`
of `X` lying over `W` at which `F` is not flat over `S` has `trdeg_{κ(f x)} κ(x) < n`. Over the
whole base this is flatness in dimensions `≥ n` (Stacks 0CWG), by the transcendence degree form
of the dimension criterion (Stacks 0CWF); over a single point `s` it is the dimension bound on
the non-flat locus of the fibre over `s`.

The relative form is what an induction which shrinks the base needs: it keeps the scheme over
the base unchanged while the open of the base over which the hypothesis is known gets smaller.

## Main definitions

* `AlgebraicGeometry.IsFlatOverInDimensionsGEOn`: flatness over the base in dimensions `≥ n`
  at the points lying over a subset of the base.
* `AlgebraicGeometry.BaseChangeFlatInDimensionsGE`: the condition defining the functor `F_n` of
  Stacks 05MU, for a family, a module and a scheme over the base.

## Main results

* `AlgebraicGeometry.isFlatOverInDimensionsGE_iff_isFlatOverInDimensionsGEOn_univ`: over the
  whole base the condition is flatness in dimensions `≥ n`.
* `AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_isFlatOverInDimensionsGEOn`:
  over a single point it is the dimension bound on the non-flat locus of the fibre.
* `AlgebraicGeometry.IsFlatOverInDimensionsGEOn.of_isPullback`: the condition is stable under
  base change.
* `AlgebraicGeometry.IsFlatOverNear.iff_forall_of_finite`: a module is flat over the base near
  every point of a fibre of a finite morphism exactly when its direct image is flat over the base
  near the image point.
* `AlgebraicGeometry.isFlatOverInDimensionsGEOn_pushforward_iff`: the condition is unchanged by
  direct image along a finite morphism.

## Implementation notes

The direct-image comparison needs, at each point, flatness at the point to agree with flatness
near it; that is openness of the relative flat locus, which Stacks 0399 provides for a module of
finite presentation over a morphism locally of finite presentation, and these are its hypotheses.
The residue field of a point is finite over the residue field of its image under a finite
morphism, so the transcendence degrees over the base agree (Stacks 06RX).

## References

* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- `F` is *flat over `S` in dimensions `≥ n` over the subset `W` of `S`* if every point `x` of
`X` with `f x ∈ W` at which `F` is not flat over `S` has `trdeg_{κ(f x)} κ(x) < n`. -/
def IsFlatOverInDimensionsGEOn {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (n : ℕ)
    (W : Set S) : Prop :=
  ∀ x : X, f x ∈ W → ¬ IsFlatOverAt f.toLRSHom.toShHom F x →
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
      WithBot ℕ∞) < (n : WithBot ℕ∞)

/-- Over the whole base, flatness in dimensions `≥ n` over a subset is flatness in dimensions
`≥ n` (Stacks 0CWF). -/
theorem isFlatOverInDimensionsGE_iff_isFlatOverInDimensionsGEOn_univ {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (n : ℕ) :
    IsFlatOverInDimensionsGE f F n ↔ IsFlatOverInDimensionsGEOn f F n Set.univ :=
  (isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt f F n).trans
    ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩

/-- Over a single point `s`, flatness in dimensions `≥ n` over `{s}` is the bound `< n` on the
dimension of the non-flat locus of the fibre over `s` (Stacks 0CWF). -/
theorem topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_isFlatOverInDimensionsGEOn
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) (s : S) :
    topologicalKrullDim
        ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} <
          (n : WithBot ℕ∞) ↔ IsFlatOverInDimensionsGEOn f F n {s} :=
  (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_at f F n s).trans
    ⟨fun h x hx ↦ h x hx, fun h x hx ↦ h x hx⟩

namespace IsFlatOverInDimensionsGEOn

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {n : ℕ} {W : Set S}

/-- The condition over a subset implies the condition over every smaller subset. -/
theorem mono (h : IsFlatOverInDimensionsGEOn f F n W) {W' : Set S} (hW : W' ⊆ W) :
    IsFlatOverInDimensionsGEOn f F n W' :=
  fun x hx ↦ h x (hW hx)

/-- The condition only depends on the isomorphism class of the module. -/
theorem of_moduleIso (h : IsFlatOverInDimensionsGEOn f F n W) {G : X.Modules} (e : F ≅ G) :
    IsFlatOverInDimensionsGEOn f G n W :=
  fun x hx hG ↦ h x hx fun hF ↦ hG ((flatOverAt_iff_of_iso f e x).mp hF)

/-- The condition is unchanged by an isomorphism of modules. -/
theorem iff_of_moduleIso {G : X.Modules} (e : F ≅ G) :
    IsFlatOverInDimensionsGEOn f F n W ↔ IsFlatOverInDimensionsGEOn f G n W :=
  ⟨fun h ↦ h.of_moduleIso e, fun h ↦ h.of_moduleIso e.symm⟩

/-- Two modules which are flat over the base at the same points over `W` are flat in dimensions
`≥ n` over `W` together. -/
theorem iff_of_isFlatOverAt_iff {G : X.Modules}
    (h : ∀ x : X, f x ∈ W →
      (IsFlatOverAt f.toLRSHom.toShHom F x ↔ IsFlatOverAt f.toLRSHom.toShHom G x)) :
    IsFlatOverInDimensionsGEOn f F n W ↔ IsFlatOverInDimensionsGEOn f G n W :=
  ⟨fun hF x hx hG ↦ hF x hx fun h' ↦ hG ((h x hx).mp h'),
    fun hG x hx hF ↦ hG x hx fun h' ↦ hF ((h x hx).mpr h')⟩

/-- The condition only depends on the morphism, not on how it is written. -/
theorem of_eq (h : IsFlatOverInDimensionsGEOn f F n W) {f' : X ⟶ S} (hf : f = f') :
    IsFlatOverInDimensionsGEOn f' F n W := hf ▸ h

/-- **Base change.** If `F` is flat over `S` in dimensions `≥ n` over `W`, then the pullback of
`F` along a base change `g : S' ⟶ S` is flat over `S'` in dimensions `≥ n` over `g⁻¹ W`. -/
theorem of_isPullback {X' S' : Scheme.{u}} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] [F.IsQuasicoherent]
    (h : IsFlatOverInDimensionsGEOn f F n W) :
    IsFlatOverInDimensionsGEOn f' ((Scheme.Modules.pullback g').obj F) n (g ⁻¹' W) := by
  intro x' hx' hnf
  have hnf' : ¬ IsFlatOverAt f.toLRSHom.toShHom F (g' x') := fun hflat ↦
    hnf (@modulePullback_isFlatOverAt X S S' X' f g g' f' hsq F ‹F.IsQuasicoherent› x' hflat)
  have hW : f (g' x') ∈ W := by
    rwa [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  exact lt_of_le_of_lt (WithBot.coe_le_coe.mpr (Cardinal.toENat.monotone'
      (trdeg_residueField_le_of_baseChange hsq x'))) (h (g' x') hW hnf')

end IsFlatOverInDimensionsGEOn

/-- The condition defining the functor `F_n` of Stacks 05MU for a family `f : X ⟶ S` and a
module `F` on `X`, at a scheme `T` over `S`: the base change of `F` to `X ×_S T` is flat over `T`
in dimensions `≥ n`, in the form of `AlgebraicGeometry.IsFlatOverInDimensionsGEOn` over the whole
of `T`. -/
abbrev BaseChangeFlatInDimensionsGE {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (n : ℕ)
    (T : Over S) : Prop :=
  IsFlatOverInDimensionsGEOn (pullback.snd f T.hom)
    ((Scheme.Modules.pullback (pullback.fst f T.hom)).obj F) n Set.univ

/-! ### Direct image along a finite morphism -/

namespace IsFlatOverNear

/-- **Flatness near a fibre of a finite morphism.** For `π : Z ⟶ Y` finite, a quasi-coherent
module `G` on `Z` is flat over `S` near every point of the fibre of `π` over `y` exactly when its
direct image `π_* G` is flat over `S` near `y`.

A finite morphism is closed, so the image of the closed complement of the locus where `G` is
flat near its points is closed, and its complement is a neighbourhood of `y` whose inverse image
lies in that locus; over it Stacks 0FLM compares the two flatness conditions. -/
theorem iff_forall_of_finite {Z Y S : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π] (q : Y ⟶ S)
    (G : Z.Modules) [G.IsQuasicoherent] (y : Y) :
    IsFlatOverNear q ((Scheme.Modules.pushforward π).obj G) y ↔
      ∀ z : Z, π z = y → IsFlatOverNear (π ≫ q) G z := by
  constructor
  · rintro hy z rfl
    rw [iff_exists_isFlatOver_restrict q ((Scheme.Modules.pushforward π).obj G) (π z)] at hy
    obtain ⟨V, hyV, hV⟩ := hy
    set W : Z.Opens := π ⁻¹ᵁ V
    have : (G.restrict W.ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor W.ι G
    have hpush : IsFlatOver (V.ι ≫ q).toLRSHom.toShHom
        ((Scheme.Modules.pushforward (π ∣_ V)).obj (G.restrict W.ι)) :=
      (isFlatOver_iff_of_iso (V.ι ≫ q)
        ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso π V).app G)).mp hV
    have hrestr :=
      (isFlatOver_pushforward_iff (π ∣_ V) (V.ι ≫ q) (G.restrict W.ι)).mpr hpush
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at hrestr
    exact ⟨W, show π z ∈ V from hyV, fun w hw ↦
      (isFlatOverAt_restrict_iff W.ι (π ≫ q) G ⟨w, hw⟩).mp (hrestr ⟨w, hw⟩)⟩
  · intro hz
    set I : Set Z := interior (flatLocus (π ≫ q) G)
    set V : Y.Opens :=
      ⟨(π.base '' Iᶜ)ᶜ, (π.isClosedMap _ isOpen_interior.isClosed_compl).isOpen_compl⟩
    have hyV : y ∈ V := by
      rintro ⟨z, hzI, hzy⟩
      exact hzI ((iff_mem_interior_flatLocus (π ≫ q) G z).mp (hz z hzy))
    have hpre : ∀ z : Z, π z ∈ V → z ∈ I := fun z hz ↦ by
      by_contra hzI
      exact hz ⟨z, hzI, rfl⟩
    rw [iff_exists_isFlatOver_restrict q ((Scheme.Modules.pushforward π).obj G) y]
    set W : Z.Opens := π ⁻¹ᵁ V
    have hrestr : IsFlatOver ((π ∣_ V) ≫ V.ι ≫ q).toLRSHom.toShHom (G.restrict W.ι) := by
      intro w
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      exact (isFlatOverAt_restrict_iff W.ι (π ≫ q) G w).2
        (interior_subset (s := flatLocus (π ≫ q) G) (hpre (W.ι w) w.2))
    have : (G.restrict W.ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor W.ι G
    have hpush := (isFlatOver_pushforward_iff (π ∣_ V) (V.ι ≫ q) (G.restrict W.ι)).mp hrestr
    exact ⟨V, hyV, (isFlatOver_iff_of_iso (V.ι ≫ q)
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso π V).app G)).mpr hpush⟩

/-- Where the relative flat locus is open, flatness near a point is flatness at it. -/
theorem iff_isFlatOverAt_of_isOpen {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (h : IsOpen (flatLocus f F)) :
    IsFlatOverNear f F x ↔ IsFlatOverAt f.toLRSHom.toShHom F x := by
  rw [iff_mem_interior_flatLocus, h.interior_eq]
  rfl

end IsFlatOverNear

/-- **Flatness at the points of a fibre of a finite morphism.** For `π : Z ⟶ Y` finite and a
module `G` of finite presentation on `Z` whose direct image is of finite presentation, over
morphisms locally of finite presentation, `G` is flat over `S` at every point of the fibre of
`π` over `y` exactly when `π_* G` is flat over `S` at `y`. -/
theorem isFlatOverAt_pushforward_iff_forall_of_finite {Z Y S : Scheme.{u}} (π : Z ⟶ Y)
    [IsFinite π] (q : Y ⟶ S) [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (π ≫ q)] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation] [((Scheme.Modules.pushforward π).obj G).IsQuasicoherent]
    [((Scheme.Modules.pushforward π).obj G).IsFinitePresentation] (y : Y) :
    IsFlatOverAt q.toLRSHom.toShHom ((Scheme.Modules.pushforward π).obj G) y ↔
      ∀ z : Z, π z = y → IsFlatOverAt (π ≫ q).toLRSHom.toShHom G z := by
  rw [← IsFlatOverNear.iff_isFlatOverAt_of_isOpen q _ y (isOpen_setOf_flatOverAt q _),
    IsFlatOverNear.iff_forall_of_finite]
  exact forall_congr' fun z ↦ imp_congr_right fun _ ↦
    IsFlatOverNear.iff_isFlatOverAt_of_isOpen (π ≫ q) G z (isOpen_setOf_flatOverAt (π ≫ q) G)

/-- **Flatness in dimensions `≥ n` is unchanged by direct image along a finite morphism.** For
`π : Z ⟶ Y` finite and a module `G` of finite presentation on `Z` whose direct image is of finite
presentation, over morphisms locally of finite presentation, `G` is flat over `S` in dimensions
`≥ n` over `W` exactly when `π_* G` is.

The non-flat points of `π_* G` are the images of the non-flat points of `G`, and the residue
field of a point of `Z` is finite over that of its image, so the transcendence degrees agree. -/
theorem isFlatOverInDimensionsGEOn_pushforward_iff {Z Y S : Scheme.{u}} (π : Z ⟶ Y)
    [IsFinite π] (q : Y ⟶ S) [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation (π ≫ q)] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation] [((Scheme.Modules.pushforward π).obj G).IsQuasicoherent]
    [((Scheme.Modules.pushforward π).obj G).IsFinitePresentation] (n : ℕ) (W : Set S) :
    IsFlatOverInDimensionsGEOn (π ≫ q) G n W ↔
      IsFlatOverInDimensionsGEOn q ((Scheme.Modules.pushforward π).obj G) n W := by
  have htr : ∀ z : Z,
      let : Algebra (S.residueField ((π ≫ q) z)) (Z.residueField z) :=
        ((π ≫ q).residueFieldMap z).hom.toAlgebra
      let : Algebra (S.residueField (q (π z))) (Y.residueField (π z)) :=
        (q.residueFieldMap (π z)).hom.toAlgebra
      Algebra.trdeg (S.residueField ((π ≫ q) z)) (Z.residueField z) =
        Algebra.trdeg (S.residueField (q (π z))) (Y.residueField (π z)) :=
    fun z ↦ trdeg_residueField_eq_of_locallyQuasiFinite π q z
  constructor
  · intro h y hy hnf
    rw [isFlatOverAt_pushforward_iff_forall_of_finite π q G y] at hnf
    push Not at hnf
    obtain ⟨z, rfl, hz⟩ := hnf
    have := h z hy hz
    rwa [htr z] at this
  · intro h z hz hnf
    have hy : ¬ IsFlatOverAt q.toLRSHom.toShHom ((Scheme.Modules.pushforward π).obj G) (π z) :=
      fun hflat ↦ hnf ((isFlatOverAt_pushforward_iff_forall_of_finite π q G (π z)).mp hflat z rfl)
    rw [htr z]
    exact h (π z) hz hy

end AlgebraicGeometry

end
