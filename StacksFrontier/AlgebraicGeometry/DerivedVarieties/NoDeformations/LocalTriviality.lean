module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.FibreIsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BaseChangeFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceLimit
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.Rigidity
import StacksCore.Tactic.StacksAttribute

/-!
# A family relatively derived equivalent to a constant family is locally constant

Let `k` be an algebraically closed field, `X` a smooth proper scheme over `k`, `f : Y ⟶ S` a
smooth proper morphism with `S` of finite type over `k`, and `K` the Fourier-Mukai kernel of a
relative equivalence from `X × S` to `Y` over `S`. Then `S` is covered by opens `U` over which
`Y` is the constant family `Y₀ × U` of a smooth proper `Y₀` over `k`. This is
[Stacks, Tag 0G0S].

## Main results

* `AlgebraicGeometry.exists_opens_iso_constantFamily_of_rationalPoint` — the source's proof at
  one `k`-rational point `s`: `Y` is the constant family with fibre `Y_s` near `s`.
* `AlgebraicGeometry.exists_opens_iso_constantFamily_of_isRelativeEquivalenceKernel` —
  **[Stacks, Tag 0G0S]**.
* `AlgebraicGeometry.isLocallyConstantFamily_of_isRelativeEquivalenceKernel` — the same, in the
  form `AlgebraicGeometry.IsLocallyConstantFamily` that the counting of [Stacks, Tag 0G11]
  consumes.

## Implementation notes

*The proof is the source's.* At a `k`-rational point `s` put `Y₀ = Y_s`. Take the partner `K'`
of `K` from [Stacks, Tag 0G0I] and restrict it to the fibre: `K'₀` on `Y₀ × X`. Pull `K'₀` back
to `M` on `(Y₀ × S) ×_S (X × S)`, and form the convolution `K_new = K ∘ M` on `(Y₀ × S) ×_S Y`.
By the compatibility of convolution with base change (the composition axiom of
[Stacks, Tag 0G0G]) the restriction of `K_new` to the fibre `Y₀ × Y₀` is the convolution of the
restrictions of `M` and `K`; the first is `K'₀` again and the convolution `K'₀ ∘ K₀` is the
restriction of `K' ∘ K ≅ Δ_{Y/S,*}𝒪_Y`, which is `Δ_{Y₀/k,*}𝒪_{Y₀}` by the identity axiom of
[Stacks, Tag 0G0G]. [Stacks, Tag 0G0R] then makes `Y` constant near `s`.

*Two simplifications against the source's text, neither changing the statement.*

1. The source first shows that `K₀ = K|_{X × Y₀}` is a relative equivalence by
   [Stacks, Tag 0G0K], takes its partner, and uses the symmetry of [Stacks, Tag 0G0I]. Here the
   partner `K'` of `K` over `S` is restricted to the fibre instead; the needed isomorphism
   `K'₀ ∘ K₀ ≅ Δ_{Y₀}` is then the base change of `K' ∘ K ≅ Δ_Y`, so neither
   [Stacks, Tag 0G0K] nor the symmetry is needed.
2. The source says `K_new` is a relative equivalence "since it is the composition of two
   invertible arrows in the category of Section 0G0F", but [Stacks, Tag 0G0R]'s proof uses only
   that the kernel is perfect (see
   `AlgebraicGeometry.exists_opens_nonempty_iso_constantFamily_of_isPerfect`). Perfectness of
   the convolution is direct over the Noetherian scheme `(Y₀ × S) ×_S Y`
   (`AlgebraicGeometry.isPerfect_fourierMukaiConvolution_of_isNoetherian`, from
   [Stacks, Tag 0B6G]), so the associativity of convolution is not needed.

*Rational points suffice.* The source chooses a closed point, which is `k`-rational since `k` is
algebraically closed. Here the pointwise statement is proved at every `k`-rational point and
`AlgebraicGeometry.isLocallyConstantFamily_of_rationalPoints` (`S` is Jacobson) turns it into the
cover of all of `S`.

*Cartesian squares rather than chosen pullbacks.* The fibre of `X × S ⟶ S` at `s` is `X` itself,
not the chosen pullback `(X × S) ×_S Spec k`; the square exhibiting this
(`AlgebraicGeometry.isPullback_sectionLift`) is cartesian because `s` is a section. All base
changes are taken along such squares with `AlgebraicGeometry.baseChangePullbackMap`, so no
    identification of
the fibre with `X` needs to be transported.

*Derived base change.* The composition and identity axioms of [Stacks, Tag 0G0G] are used at
arbitrary cartesian squares, as `AlgebraicGeometry.convolutionBaseChangeIsoOfIsPullback` and
`AlgebraicGeometry.isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel`, with
[Stacks, Tag 08IB] supplied by `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`.
Nothing is granted.

## References

* [Stacks Project, Tag 0G0S](https://stacks.math.columbia.edu/tag/0G0S)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0G0G](https://stacks.math.columbia.edu/tag/0G0G)
* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Section

universe v' u'

variable {C : Type u'} [Category.{v'} C] [HasPullbacks C] {X B S : C}
  (a : X ⟶ B) (q : S ⟶ B) (t : B ⟶ S) (ht : t ≫ q = 𝟙 B)

/-- The morphism `X ⟶ X ×_B S` given by `𝟙 X` and `X ⟶ B ⟶ S`, for a section `t` of `q`. -/
def sectionLift : X ⟶ pullback a q :=
  pullback.lift (𝟙 X) (a ≫ t) (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id])

/-- The composite of `sectionLift a q t ht` with the first projection is `𝟙 X`. -/
@[reassoc (attr := simp)]
lemma sectionLift_fst : sectionLift a q t ht ≫ pullback.fst a q = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The composite of `sectionLift a q t ht` with the second projection is `a ≫ t`. -/
@[reassoc (attr := simp)]
lemma sectionLift_snd : sectionLift a q t ht ≫ pullback.snd a q = a ≫ t :=
  pullback.lift_snd _ _ _

/-- **The fibre of `X ×_B S ⟶ S` along a section `t` of `q : S ⟶ B` is `X`.** The square with
top `sectionLift`, sides `a` and `X ×_B S ⟶ S`, and bottom `t` is cartesian: pasted with the
pullback square of `X ×_B S` it is the trivial square on `a`, because `t ≫ q = 𝟙 B`. -/
lemma isPullback_sectionLift : IsPullback (sectionLift a q t ht) a (pullback.snd a q) t := by
  refine IsPullback.of_right ?_ (sectionLift_snd a q t ht) (IsPullback.of_hasPullback a q)
  rw [sectionLift_fst, ht]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

end Section

section Transport

variable {U V : Scheme.{u}}

/-- **Derived pullback along a composite equal to the identity.** If `p ≫ r = 𝟙 U` then
`L p^* L r^* E ≅ E`, by [Stacks, Tag 0D5S] and `L(𝟙)^* ≅ 𝟭`. -/
def dpullCompIsoSelfOfCompEqId (p : U ⟶ V) (r : V ⟶ U) (h : p ≫ r = 𝟙 U)
    (E : DerivedCategory U.Modules) : (dpull p).obj ((dpull r).obj E) ≅ E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      p.toLRSHom.toShHom r.toLRSHom.toShHom).app E ≪≫
    eqToIso (by rw [← shHom_comp, h]; rfl) ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso U.toRingedSpace).app E

end Transport

section RationalPoint

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (a : X ⟶ Spec (.of k)) (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (t : Spec (.of k) ⟶ S)

/-- The comparison `Y_s ×_k Y_s ⟶ (Y_s ×_k S) ×_S Y` of [Stacks, Tag 0G0R] is the base-change
comparison of the two cartesian squares exhibiting `Y_s` as the fibre at `s` of the constant
family and of `Y`. -/
lemma fibreSquareToProductComparison_eq_bcMap (ht : t ≫ q = 𝟙 _) :
    fibreSquareToProductComparison q g t ht =
      baseChangePullbackMap (isPullback_sectionLift (fibreAtRationalPointπ g t) q t ht).toCommSq
        (IsPullback.of_hasPullback g t).toCommSq := by
  have hc : pullback.fst g t ≫ g = pullback.snd g t ≫ t := pullback.condition
  have hd : pullback.fst (fibreAtRationalPointπ g t) (fibreAtRationalPointπ g t) ≫
      fibreAtRationalPointπ g t =
      pullback.snd (fibreAtRationalPointπ g t) (fibreAtRationalPointπ g t) ≫
        fibreAtRationalPointπ g t := pullback.condition
  apply pullback.hom_ext
  · rw [baseChangePullbackMap_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, sectionLift_fst, Category.comp_id,
        ← Category.assoc, fibreSquareToProductComparison_comp_fst_fst]
    · rw [Category.assoc, Category.assoc, sectionLift_snd, fibreSquareToProductComparison,
        pullback.lift_fst_assoc, pullback.lift_snd]
      simp only [fibreAtRationalPointι, fibreAtRationalPointπ] at hd ⊢
      rw [hc, ← Category.assoc, ← hd, Category.assoc]
  · rw [baseChangePullbackMap_snd, fibreSquareToProductComparison_comp_snd]

variable [Smooth a] [IsProper a] [LocallyOfFiniteType q] [QuasiCompact q] [Smooth g] [IsProper g]

/-- **[Stacks, Tag 0G0S] at one `k`-rational point.** Let `X ⟶ Spec k` and
`g : Y ⟶ S` be smooth and proper, `S` of finite type over `k`, and `K` the Fourier-Mukai kernel
of a relative equivalence from `X ×_k S` to `Y` over `S`. For every `k`-rational point
`s : Spec k ⟶ S` there is an open `U ⊆ S` containing the point `s` picks out with `Y|_U`
isomorphic to the constant family `Y_s ×_k U` over `U`.

No algebraic closedness is needed at a rational point. The proof is the source's; see the
module docstring. -/
theorem exists_opens_iso_constantFamily_of_rationalPoint
    (ht : t ≫ q = 𝟙 _)
    (K : DerivedCategory (pullback (pullback.snd a q) g).Modules)
    (hK : IsRelativeEquivalenceKernel (pullback.snd a q) g K) :
    ∃ U : S.Opens, Set.range t.base ⊆ (U : Set S) ∧
      Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅
        Over.mk (pullback.snd (fibreAtRationalPointπ g t) (U.ι ≫ q))) := by
  obtain ⟨hKp, K', hK'p, -, ⟨e₂⟩⟩ := hK
  -- the cartesian squares
  have hXt := isPullback_sectionLift a q t ht
  have hYt := IsPullback.of_hasPullback g t
  have hCt := isPullback_sectionLift (fibreAtRationalPointπ g t) q t ht
  have hCq := IsPullback.of_hasPullback (fibreAtRationalPointπ g t) q
  have hXq := IsPullback.of_hasPullback a q
  -- quasi-coherence of the two kernels over `S`
  have hKq : IsQCohAll K := PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K hKp
  have hK'q : IsQCohAll K' :=
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK'p
  -- `K'₀` on `Y_s ×_k X`, and `M` on `(Y_s ×_k S) ×_S (X ×_k S)`
  let K'₀ := (dpull (baseChangePullbackMap hYt.toCommSq hXt.toCommSq)).obj K'
  let M := (dpull (baseChangePullbackMap hCq.toCommSq hXq.toCommSq)).obj K'₀
  have hMp : IsPerfect (X := (pullback (constantFamilyπ q g t) (pullback.snd a q)).toRingedSpace)
      M :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K' hK'p)
  have hMq : IsQCohAll M := isQCohAll_dpull _ (isQCohAll_dpull _ hK'q)
  -- the new kernel
  let Knew := fourierMukaiConvolution (constantFamilyπ q g t) (pullback.snd a q) g M K
  have hnoeth : IsNoetherian (pullback (constantFamilyπ q g t) g) := by
    have := isLocallyNoetherian_fibreProduct q g t
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
    have := isProper_constantFamilyProductToBase q g t
    have := QuasiCompact.compactSpace_of_compactSpace (constantFamilyProductToBase q g t)
    exact ⟨⟩
  -- the restriction of `M` to the fibre is `K'₀`
  have hcomp : baseChangePullbackMap hCt.toCommSq hXt.toCommSq ≫
      baseChangePullbackMap hCq.toCommSq hXq.toCommSq = 𝟙 _ :=
    pullback.hom_ext (by simp) (by simp)
  -- the restriction of the new kernel to the fibre is the diagonal kernel
  have restrict : Nonempty ((derivedPullback
      (fibreSquareToProductComparison q g t ht).toLRSHom.toShHom).obj Knew ≅
        diagonalKernel (fibreAtRationalPointπ g t)) := by
    rw [fibreSquareToProductComparison_eq_bcMap q g t ht]
    obtain ⟨eΔ⟩ := isIsomorphic_fourierMukaiBaseChangeKernel_diagonalKernel g t
    exact ⟨convolutionBaseChangeIsoOfIsPullback hCt hXt hYt hMq hKq ≪≫
      fourierMukaiConvolutionMapIso _ _ _ (dpullCompIsoSelfOfCompEqId _ _ hcomp K'₀) (Iso.refl _) ≪≫
      (convolutionBaseChangeIsoOfIsPullback hYt hXt hYt hK'q hKq).symm ≪≫
      (dpull (baseChangePullbackMap hYt.toCommSq hYt.toCommSq)).mapIso e₂.symm ≪≫ eΔ⟩
  exact exists_opens_nonempty_iso_constantFamily_of_isPerfect q g t ht Knew
    (isPerfect_fourierMukaiConvolution_of_isNoetherian _ _ _ hMp hKp) restrict

/-- **[Stacks, Tag 0G0S].** Let `k` be algebraically closed, `X ⟶ Spec k`
smooth and proper, `g : Y ⟶ S` smooth and proper with `S` of finite type over `k`, and `K` the
Fourier-Mukai kernel of a relative equivalence from `X ×_k S` to `Y` over `S`. Then every point of
`S` has an open neighbourhood `U` over which `Y` is the constant family `Y₀ ×_k U` of some smooth
proper `Y₀` over `k`.

At each `k`-rational point `s` this is `exists_opens_iso_constantFamily_of_rationalPoint` with
`Y₀ = Y_s`, smooth and proper as a base change of `g`; the opens so obtained cover `S` by
`AlgebraicGeometry.exists_mem_opens_of_rationalPoints` (`S` is Jacobson and its closed points
are `k`-rational). -/
@[stacks 0G0S]
theorem exists_opens_iso_constantFamily_of_isRelativeEquivalenceKernel [IsAlgClosed k]
    (K : DerivedCategory (pullback (pullback.snd a q) g).Modules)
    (hK : IsRelativeEquivalenceKernel (pullback.snd a q) g K) :
    ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ ∃ Y₀ : Over (Spec (.of k)),
      Smooth Y₀.hom ∧ IsProper Y₀.hom ∧
        Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅ (Over.pullback (U.ι ≫ q)).obj Y₀) := by
  refine exists_mem_opens_of_rationalPoints q _ fun t ht => ?_
  obtain ⟨U, hU, e⟩ := exists_opens_iso_constantFamily_of_rationalPoint a q g t ht K hK
  exact ⟨U, hU, Over.mk (fibreAtRationalPointπ g t),
    (inferInstance : Smooth (fibreAtRationalPointπ g t)),
    (inferInstance : IsProper (fibreAtRationalPointπ g t)), e⟩

/-- **[Stacks, Tag 0G0S] as a locally constant family**: in the situation of
`exists_opens_iso_constantFamily_of_isRelativeEquivalenceKernel`, `Y ⟶ S` is an
`AlgebraicGeometry.IsLocallyConstantFamily` over `k`. This forgets that the fibres `Y₀` are smooth
and proper, which the counting of [Stacks, Tag 0G11] does not use. -/
theorem isLocallyConstantFamily_of_isRelativeEquivalenceKernel [IsAlgClosed k]
    (K : DerivedCategory (pullback (pullback.snd a q) g).Modules)
    (hK : IsRelativeEquivalenceKernel (pullback.snd a q) g K) :
    IsLocallyConstantFamily q (Over.mk g) := fun x =>
  (exists_opens_iso_constantFamily_of_isRelativeEquivalenceKernel a q g K hK x).imp
    fun _ ⟨hx, Y₀, _, _, e⟩ => ⟨hx, Y₀, e⟩

end RationalPoint

end AlgebraicGeometry

end
