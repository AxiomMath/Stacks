module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing

/-!
# Lifting a point of prescribed relative transcendence degree along a base change

Let `f : X ⟶ S` be locally of finite type and let `x : X` be a point whose residue field has
transcendence degree `r` over the residue field of `f x`. If `g : S' ⟶ S` is surjective and
`f' : X' ⟶ S'` is the base change of `f`, then `x` has a preimage `x' : X'` with the same
relative transcendence degree. Any two such preimages are the two images of a single point of
the base change `f'' : X'' ⟶ S''` of `f` to `S'' = S' ×_S S'`, again with the same relative
transcendence degree.

## Main results

* `AlgebraicGeometry.exists_preimage_preserving_residueField_trdeg`: a preimage of the same
  relative transcendence degree exists after a surjective base change.
* `AlgebraicGeometry.exists_common_preimage_preserving_residueField_trdeg`: two such preimages
  have a common preimage of the same relative transcendence degree over the double base change.

## References

* [Stacks Project, Tag 0H4W](https://stacks.math.columbia.edu/tag/0H4W)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Reading the local dimension of the fibre of the morphism of fibres induced by a commutative
square does not depend on the equality used to place a point of the source in a fibre. -/
private lemma ringKrullDim_stalk_fiber_fiberMap_of_apply_eq {U' U V' V : Scheme.{u}}
    (f' : U' ⟶ V') (g' : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V) (h : g' ≫ f = f' ≫ g)
    (u : U') (v : V') (e : f' u = v) :
    ringKrullDim (((fiberMap f' g' g f h v).fiber
            (fiberMap f' g' g f h v ((f'.fiberHomeo v).symm ⟨u, e⟩))).presheaf.stalk
          ((fiberMap f' g' g f h v).asFiber ((f'.fiberHomeo v).symm ⟨u, e⟩))) =
      ringKrullDim (((fiberMap f' g' g f h (f' u)).fiber
            (fiberMap f' g' g f h (f' u) (f'.asFiber u))).presheaf.stalk
          ((fiberMap f' g' g f h (f' u)).asFiber (f'.asFiber u))) := by
  subst e
  rfl

/-- The morphism of fibres induced by a commutative square sits over the left vertical arrow of
that square, read on points. -/
public lemma fiberMap_fiberι_apply {U' U V' V : Scheme.{u}} (f' : U' ⟶ V') (g' : U' ⟶ U)
    (g : V' ⟶ V) (f : U ⟶ V) (h : g' ≫ f = f' ≫ g) (v' : V') (a : f'.fiber v') :
    f.fiberι (g v') (fiberMap f' g' g f h v' a) = g' (f'.fiberι v' a) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fiberMap_fiberι f' g' g f h v']

/-- Every point of a scheme is a specialisation of a point whose local ring is zero-dimensional. -/
public lemma exists_specializes_ringKrullDim_stalk_eq_zero (Y : Scheme.{u}) (y : Y) :
    ∃ z : Y, z ⤳ y ∧ ringKrullDim (Y.presheaf.stalk z) = 0 := by
  obtain ⟨R, j, hj, hjy⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Y) (x := y) (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨q, hq⟩ := Set.mem_range.mp hjy.1
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal R)) (J := q.asIdeal) bot_le
  have : p.IsPrime := hp.isPrime
  let p' : Spec R := ⟨p, hp.isPrime⟩
  have hspec : j p' ⤳ j q :=
    j.isOpenEmbedding.isInducing.specializes_iff.mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mp hpq)
  refine ⟨j p', hq ▸ hspec, ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion j,
    ← idealHeight_eq_coheight R p']
  simp [p', Ideal.height_eq_zero_iff.mpr hp]

/-- A point whose local ring is zero-dimensional has no proper generalisations. -/
public lemma eq_of_specializes_of_ringKrullDim_stalk_eq_zero {Y : Scheme.{u}} {a b : Y}
    (hab : a ⤳ b) (hb : ringKrullDim (Y.presheaf.stalk b) = 0) : a = b := by
  have hcb : Order.coheight b = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hb
    exact WithBot.coe_eq_coe.mp hb
  exact (hab.antisymm (Scheme.le_iff_specializes.mp
    ((Order.coheight_eq_zero.mp hcb) (Scheme.le_iff_specializes.mpr hab)))).eq

section BaseChange

variable {X'' X' X S'' S' S : Scheme.{u}}

/-- Let `f : X ⟶ S` be locally of finite type, let
`g : S' ⟶ S` be surjective and let `f' : X' ⟶ S'` be the base change of `f`. A point `x : X`
whose residue field has transcendence degree `r` over the residue field of `f x` has a preimage
in `X'` whose residue field has transcendence degree `r` over the residue field of its image in
`S'`. -/
@[stacks 0H4W "part (1)", sga "2 XIV 2.1.1" "special case"]
public theorem exists_preimage_preserving_residueField_trdeg {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hpb : IsPullback p f' f g) [LocallyOfFiniteType f] [Surjective g]
    (r : ℕ) (x : X)
    (hr : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.trdeg ↥(S.residueField (f x)) ↥(X.residueField x) = r) :
    ∃ (x' : X') (_hx : p x' = x),
      letI := (f'.residueFieldMap x').hom.toAlgebra
      Algebra.trdeg ↥(S'.residueField (f' x')) ↥(X'.residueField x') = r := by
  obtain ⟨s', hgs⟩ := Scheme.Hom.surjective g (f x)
  obtain ⟨x', hx, hsx, -, htr⟩ :=
    exists_pullback_point_preserving_fibre_dimension_and_trdeg hpb s' x hgs.symm
  refine ⟨x', hx, ?_⟩
  let : Algebra ↥(S.residueField (g s')) ↥(X.residueField x) :=
    ((S.residueFieldCongr hgs.symm).inv ≫ f.residueFieldMap x).hom.toAlgebra
  let : Algebra ↥(S'.residueField s') ↥(X'.residueField x') :=
    ((S'.residueFieldCongr hsx).inv ≫ f'.residueFieldMap x').hom.toAlgebra
  calc
    @Algebra.trdeg _ _ _ _ (f'.residueFieldMap x').hom.toAlgebra =
        Algebra.trdeg ↥(S'.residueField s') ↥(X'.residueField x') :=
      (trdeg_residueFieldMap_congr f' x' s' hsx).symm
    _ = Algebra.trdeg ↥(S.residueField (g s')) ↥(X.residueField x) := htr.symm
    _ = @Algebra.trdeg _ _ _ _ (f.residueFieldMap x).hom.toAlgebra :=
      trdeg_residueFieldMap_congr f x (g s') hgs.symm
    _ = r := hr

/-- Let `S''` be the self-intersection `S' ×_S S'` of the base change, with projections `q₁` and
`q₂`, and let `f'' : X'' ⟶ S''` be the base change of `f` to `S''`, with projections `p₁` and `p₂`
to `X'` exhibiting `X''` as `X' ×_X X'`. Let `x₁'` and `x₂'` be two preimages of a point `x` of
relative transcendence degree `r`, the first of transcendence degree `r` again and the second of
transcendence degree `d`. Then `x₁'` and `x₂'` are the two images of a point of `X''` of
transcendence degree `d` over the residue field of its image in `S''`. -/
public theorem exists_common_preimage_of_preserved_trdeg {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} {q₁ q₂ : S'' ⟶ S'} {p₁ p₂ : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    (hX' : IsPullback p f' f g) (_hS'' : IsPullback q₁ q₂ g g)
    (hX''₁ : IsPullback p₁ f'' f' q₁) (hX''₂ : IsPullback p₂ f'' f' q₂)
    (hXX : IsPullback p₁ p₂ p p) [LocallyOfFiniteType f] (r d : ℕ) (x : X) (x₁' x₂' : X')
    (hr : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.trdeg ↥(S.residueField (f x)) ↥(X.residueField x) = r)
    (hx₁ : p x₁' = x) (hx₂ : p x₂' = x)
    (hr₁ : letI := (f'.residueFieldMap x₁').hom.toAlgebra
      Algebra.trdeg ↥(S'.residueField (f' x₁')) ↥(X'.residueField x₁') = r)
    (hr₂ : letI := (f'.residueFieldMap x₂').hom.toAlgebra
      Algebra.trdeg ↥(S'.residueField (f' x₂')) ↥(X'.residueField x₂') = d) :
    ∃ x'' : X'', p₁ x'' = x₁' ∧ p₂ x'' = x₂' ∧
      (letI := (f''.residueFieldMap x'').hom.toAlgebra
       Algebra.trdeg ↥(S''.residueField (f'' x'')) ↥(X''.residueField x'') = d) := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hX' inferInstance
  have : LocallyOfFiniteType f'' := MorphismProperty.of_isPullback hX''₂ inferInstance
  obtain ⟨z₀, hz₁, hz₂⟩ :=
    Scheme.exists_preimage_of_isPullback hXX x₁' x₂' (hx₁.trans hx₂.symm)
  let s'' := f'' z₀
  have hs₁ : q₁ s'' = f' x₁' := (congr($(hX''₁.w) z₀)).symm.trans (congrArg f' hz₁)
  let φ := fiberMap f'' p₂ q₂ f' hX''₂.w s''
  let y₀ : f''.fiber s'' := (f''.fiberHomeo s'').symm ⟨z₀, rfl⟩
  have hφ_under (a : f''.fiber s'') :
      f'.fiberι (q₂ s'') (φ a) = p₂ (f''.fiberι s'' a) :=
    fiberMap_fiberι_apply f'' p₂ q₂ f' hX''₂.w s'' a
  let c₀ := (φ.fiberHomeo (φ y₀)).symm ⟨y₀, rfl⟩
  obtain ⟨z, hspec, hzero⟩ :=
    exists_specializes_ringKrullDim_stalk_eq_zero (φ.fiber (φ y₀)) c₀
  let a := φ.fiberι (φ y₀) z
  let x'' := f''.fiberι s'' a
  have hxbase : f'' x'' = s'' := (f''.fiberHomeo s'' a).2
  have hφa : φ a = φ y₀ := (φ.fiberHomeo (φ y₀) z).2
  have hp₂ : p₂ x'' = x₂' :=
    calc
      p₂ x'' = f'.fiberι (q₂ s'') (φ a) := (hφ_under a).symm
      _ = f'.fiberι (q₂ s'') (φ y₀) := congrArg (f'.fiberι (q₂ s'')) hφa
      _ = p₂ (f''.fiberι s'' y₀) := hφ_under y₀
      _ = p₂ z₀ := congrArg p₂ (by simp [y₀])
      _ = x₂' := hz₂
  have hspecX'' : x'' ⤳ z₀ := by
    have ha : a ⤳ y₀ := by simpa [a, c₀] using hspec.map (φ.fiberι (φ y₀)).continuous
    simpa [x'', y₀] using ha.map (f''.fiberι s'').continuous
  have hspec₁ : p₁ x'' ⤳ x₁' := by simpa [hz₁] using hspecX''.map p₁.continuous
  have hp₁ : p₁ x'' = x₁' := by
    let s₁ := f' x₁'
    let ψ := fiberMap f' p g f hX'.w s₁
    let b₁ : f'.fiber s₁ := f'.asFiber x₁'
    have hb₁ : f'.fiberι s₁ b₁ = x₁' := by simp [b₁, s₁]
    have hybase : f' (p₁ x'') = s₁ :=
      (congr($(hX''₁.w) x'')).trans
        ((congrArg q₁ hxbase).trans hs₁)
    have hpbase : p (p₁ x'') = x :=
      (congr($(hXX.w) x'')).trans ((congrArg p hp₂).trans hx₂)
    have hψ_under (b : f'.fiber s₁) :
        f.fiberι (g s₁) (ψ b) = p (f'.fiberι s₁ b) :=
      fiberMap_fiberι_apply f' p g f hX'.w s₁ b
    let a₁ : f'.fiber s₁ := (f'.fiberHomeo s₁).symm ⟨p₁ x'', hybase⟩
    have hψa : ψ a₁ = ψ b₁ := by
      apply (f.fiberι (g s₁)).isEmbedding.injective
      calc
        f.fiberι (g s₁) (ψ a₁) = p (p₁ x'') := by rw [hψ_under]; simp [a₁]
        _ = x := hpbase
        _ = p x₁' := hx₁.symm
        _ = f.fiberι (g s₁) (ψ b₁) := by rw [hψ_under]; exact congrArg p hb₁.symm
    have hspecA : a₁ ⤳ b₁ :=
      ((f'.fiberHomeo s₁).symm.isInducing.specializes_iff).mpr
        ((subtype_specializes_iff _ _).2 (by simpa [a₁, b₁, s₁] using hspec₁))
    have hspecD : (ψ.fiberHomeo (ψ b₁)).symm ⟨a₁, hψa⟩ ⤳ ψ.asFiber b₁ :=
      ((ψ.fiberHomeo (ψ b₁)).symm.isInducing.specializes_iff).mpr
        ((subtype_specializes_iff _ _).2 (by simpa using hspecA))
    have hdim₁ : ringKrullDim ((ψ.fiber (ψ b₁)).presheaf.stalk (ψ.asFiber b₁)) = 0 := by
      let : Algebra ↥(S.residueField (f x)) ↥(X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      let : Algebra ↥(S.residueField (f (p x₁'))) ↥(X.residueField (p x₁')) :=
        (f.residueFieldMap (p x₁')).hom.toAlgebra
      let : Algebra ↥(S'.residueField (f' x₁')) ↥(X'.residueField x₁') :=
        (f'.residueFieldMap x₁').hom.toAlgebra
      have hdim := fiberMap_ringKrullDim_stalk_add_trdeg_eq hX' x₁'
      dsimp only at hdim
      rw [hx₁, hr, hr₁] at hdim
      exact (ENat.WithBot.add_natCast_cancel (c := r)).mp (by simpa [ψ, b₁, s₁] using hdim)
    have ha₁ : a₁ = b₁ := by
      simpa using congrArg (ψ.fiberι (ψ b₁))
        (eq_of_specializes_of_ringKrullDim_stalk_eq_zero hspecD hdim₁)
    simpa [a₁, b₁, s₁] using congrArg (f'.fiberι s₁) ha₁
  refine ⟨x'', hp₁, hp₂, ?_⟩
  let : Algebra ↥(S''.residueField (f'' x'')) ↥(X''.residueField x'') :=
    (f''.residueFieldMap x'').hom.toAlgebra
  let : Algebra ↥(S'.residueField (f' (p₂ x''))) ↥(X'.residueField (p₂ x'')) :=
    (f'.residueFieldMap (p₂ x'')).hom.toAlgebra
  have hpt : (φ.fiberHomeo (φ y₀)).symm ⟨a, hφa⟩ = z := by
    apply (φ.fiberι (φ y₀)).isEmbedding.injective
    simp [a]
  have hzero' : ringKrullDim ((φ.fiber (φ a)).presheaf.stalk (φ.asFiber a)) = 0 := by
    rwa [← ringKrullDim_stalk_fiberHomeo_symm φ a (φ y₀) hφa, hpt]
  let yx := (f''.fiberHomeo s'').symm ⟨x'', hxbase⟩
  have hyfiber : yx = a := by
    apply (f''.fiberι s'').isEmbedding.injective
    rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  have hzeroAtS : ringKrullDim ((φ.fiber (φ yx)).presheaf.stalk (φ.asFiber yx)) = 0 := by
    rwa [hyfiber]
  let φ' := fiberMap f'' p₂ q₂ f' hX''₂.w (f'' x'')
  have hzero'' : ringKrullDim ((φ'.fiber (φ' (f''.asFiber x''))).presheaf.stalk
      (φ'.asFiber (f''.asFiber x''))) = 0 := by
    rw [← ringKrullDim_stalk_fiber_fiberMap_of_apply_eq f'' p₂ q₂ f' hX''₂.w x'' s'' hxbase]
    simpa [φ, φ', yx, hyfiber] using hzeroAtS
  have hdim := fiberMap_ringKrullDim_stalk_add_trdeg_eq hX''₂ x''
  dsimp only at hdim
  rw [hzero'', zero_add] at hdim
  let : Algebra.EssFiniteType ↥(S''.residueField (f'' x'')) ↥(X''.residueField x'') :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f'' x'')
  let : Algebra.EssFiniteType ↥(S'.residueField (f' (p₂ x'')))
      ↥(X'.residueField (p₂ x'')) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f' (p₂ x''))
  calc
    @Algebra.trdeg _ _ _ _ (f''.residueFieldMap x'').hom.toAlgebra =
        @Algebra.trdeg _ _ _ _ (f'.residueFieldMap (p₂ x'')).hom.toAlgebra :=
      (Cardinal.toENat_eq_iff_of_le_aleph0 (trdeg_lt_aleph0 _ _).le
        (trdeg_lt_aleph0 _ _).le).mp (by exact_mod_cast hdim)
    _ = @Algebra.trdeg _ _ _ _ (f'.residueFieldMap x₂').hom.toAlgebra :=
      congrArg (fun y : X' ↦ @Algebra.trdeg _ _ _ _ (f'.residueFieldMap y).hom.toAlgebra) hp₂
    _ = d := hr₂

/-- In the situation of `AlgebraicGeometry.exists_preimage_preserving_residueField_trdeg`, let
`S''` be the self-intersection `S' ×_S S'` of the base change, with projections `q₁` and `q₂`,
and let `f'' : X'' ⟶ S''` be the base change of `f` to `S''`, with projections `p₁` and `p₂` to
`X'` exhibiting `X''` as `X' ×_X X'`. Two preimages `x₁'` and `x₂'` of `x` of the same relative
transcendence degree `r` are the two images of a point of `X''` whose residue field again has
transcendence degree `r` over the residue field of its image in `S''`. -/
@[stacks 0H4W "part (2)"]
public theorem exists_common_preimage_preserving_residueField_trdeg {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} {q₁ q₂ : S'' ⟶ S'} {p₁ p₂ : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    (hX' : IsPullback p f' f g) (hS'' : IsPullback q₁ q₂ g g)
    (hX''₁ : IsPullback p₁ f'' f' q₁) (hX''₂ : IsPullback p₂ f'' f' q₂)
    (hXX : IsPullback p₁ p₂ p p) [LocallyOfFiniteType f] (r : ℕ) (x : X) (x₁' x₂' : X')
    (hr : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.trdeg ↥(S.residueField (f x)) ↥(X.residueField x) = r)
    (hx₁ : p x₁' = x) (hx₂ : p x₂' = x)
    (hr₁ : letI := (f'.residueFieldMap x₁').hom.toAlgebra
      Algebra.trdeg ↥(S'.residueField (f' x₁')) ↥(X'.residueField x₁') = r)
    (hr₂ : letI := (f'.residueFieldMap x₂').hom.toAlgebra
      Algebra.trdeg ↥(S'.residueField (f' x₂')) ↥(X'.residueField x₂') = r) :
    ∃ x'' : X'', p₁ x'' = x₁' ∧ p₂ x'' = x₂' ∧
      (letI := (f''.residueFieldMap x'').hom.toAlgebra
       Algebra.trdeg ↥(S''.residueField (f'' x'')) ↥(X''.residueField x'') = r) :=
  exists_common_preimage_of_preserved_trdeg hX' hS'' hX''₁ hX''₂ hXX r r x x₁' x₂' hr hx₁ hx₂
    hr₁ hr₂

end BaseChange

end AlgebraicGeometry
