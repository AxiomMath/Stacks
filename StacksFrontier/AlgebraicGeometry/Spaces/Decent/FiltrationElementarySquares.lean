module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds

/-!
# The finite filtration of a quasi-compact quasi-separated space by elementary squares

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S` in a big fppf
site. Stacks 07ST filters `X` by finitely many open subspaces
`X = U 0 ⊇ U 1 ⊇ ⋯ ⊇ U n = ∅` such that each reduced stratum `U p ∖ U (p + 1)` has a
quasi-compact separated scheme `V p` as a surjective étale neighbourhood `f p : V p ⟶ U p`
which is an isomorphism above the stratum. Read through Stacks 08GM, every step of that
filtration is an elementary distinguished square on `U p` whose open member is `U (p + 1)`.
This file records the filtration in that form, which is the shape a descending induction over
it consumes, and bounds the size of every `V p` by the size of any surjective étale atlas of
`X`.

## Main results

* `AlgebraicGeometry.Space.size_le_of_isEtale_of_atlas`: if `a : yoneda.obj A ⟶ X` is a
  surjective étale atlas of an algebraic space `X`, then every quasi-compact scheme `V` of the
  site with an étale morphism `yoneda.obj V ⟶ X` has `size V ≤ size A`.
* `AlgebraicGeometry.Space.exists_finiteFiltration_isElementaryDistinguishedSquare`: the
  filtration of Stacks 07ST as a finite chain of elementary distinguished squares, with the
  size of each étale member bounded by the size of a given surjective étale atlas.

## Implementation notes

The open member of the square on `U p` is `U (p + 1)` read as a subfunctor of `U p`, that is
its preimage along the inclusion of `U p`; it agrees with the range of the inclusion
`U (p + 1) ⟶ U p`, which is the form in which
`AlgebraicGeometry.Space.isElementaryDistinguishedSquare_of_reducedStratum` produces the
square from the data of Stacks 07ST.

The size bound passes through the represented fibre product `P = V ×_X A`. Its projection to
`V` is a base change of the atlas, hence surjective and étale, and its projection to `A` is a
base change of the étale morphism `V ⟶ X`, hence locally of finite type. Since `V` is
quasi-compact, `AlgebraicGeometry.size_le_of_compact_of_fppf_factorsThrough` bounds `size V`
by `size A`.

## References

* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

/-- **The size of a quasi-compact scheme étale over an algebraic space is bounded by the size of
any surjective étale atlas.** Let `a : yoneda.obj A ⟶ X` be surjective and étale, and let
`g : yoneda.obj V ⟶ X` be étale with `V` quasi-compact. Then `size V ≤ size A`.

The represented fibre product `V ×_X A` maps to `V` by a surjective étale morphism, a base
change of `a`, and to `A` by an étale morphism, a base change of `g`. -/
theorem size_le_of_isEtale_of_atlas (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A V : BigFppfOver B S hS} {a : yoneda.obj A ⟶ X}
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : IsEtale B S hS a)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj V)]
    {g : yoneda.obj V ⟶ X} (hg : IsEtale B S hS g) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      ((BigFppfOver.toScheme B S hS).obj A).size := by
  let q := BigFppfOver.toScheme B S hS
  have haE := (isEtale_iff_presheaf_of_yoneda B S hS a).1 haEtale
  have hgE := (isEtale_iff_presheaf_of_yoneda B S hS g).1 hg
  have hs : Surjective (q.map (haSurj.rep.snd g)) := haSurj.property_snd g
  have he : Etale (q.map (haSurj.rep.snd g)) :=
    haE.property g (haSurj.rep.fst g) (haSurj.rep.snd g) (haSurj.rep.isPullback g)
  have hp : Etale (q.map (haSurj.rep.fst' g)) :=
    hgE.property a (yoneda.map (haSurj.rep.snd g)) (haSurj.rep.fst' g)
      (haSurj.rep.isPullback' g).flip
  let E : FppfCovering.{0} (q.obj V) :=
    ⟨PUnit, fun _ => q.obj (haSurj.rep.pullback g), fun _ => q.map (haSurj.rep.snd g),
      fun _ => inferInstance, fun _ => inferInstance,
      fun v => by obtain ⟨x, hx⟩ := hs.surj v; exact ⟨PUnit.unit, x, hx⟩⟩
  exact size_le_of_compact_of_fppf_factorsThrough (q.map (haSurj.rep.fst' g))
    (q.map (haSurj.rep.snd g)) E (fun _ => 𝟙 _) (fun _ => Category.id_comp _)

/-- The range of the inclusion of one subfunctor into a larger one is the preimage of the
smaller subfunctor along the inclusion of the larger. -/
private theorem range_homOfLe_eq_preimage {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u}
    {I J : Subfunctor F} (h : I ≤ J) :
    Subfunctor.range (Subfunctor.homOfLe h) = I.preimage J.ι := by
  refine Subfunctor.ext (funext fun T => Set.ext fun x => ⟨?_, fun hx => ⟨⟨x.1, hx⟩, rfl⟩⟩)
  rintro ⟨y, rfl⟩
  exact y.2

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The filtration of Stacks 07ST as a chain of elementary distinguished squares.** Let `X`
be a quasi-compact quasi-separated algebraic space with a surjective étale atlas
`a : yoneda.obj A ⟶ X`. There are a natural number `n`, open subspaces
`X = U 0 ⊇ U 1 ⊇ ⋯ ⊇ U n` with `U n` empty, and for each `p < n` a quasi-compact separated
scheme `V p` of the site with a surjective étale morphism `f p : V p ⟶ U p`, such that
`U (p + 1)`, read as a subfunctor of `U p`, and `f p` form an elementary distinguished square
on `U p`. Moreover each `U p` is quasi-compact and `size (V p) ≤ max ℵ₀ (size A)`. -/
theorem exists_finiteFiltration_isElementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ X)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : IsEtale B S hS a) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X) (V : Fin n → BigFppfOver B S hS)
      (f : ∀ p : Fin n, yoneda.obj (V p) ⟶ (U p.val).toFunctor),
      U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS) ∧
      Nonempty ((U n).toFunctor ≅ yoneda.obj (BigFppfOver.initialObj B S hS)) ∧
      (∀ p ≤ n, IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∀ p : Fin n,
        (∃ hW : IsAlgebraicSpace B S hS (U p.val).toFunctor,
          IsElementaryDistinguishedSquare B S hS hW
            ((U (p.val + 1)).preimage (U p.val).ι) (f p)) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (f p) ∧
        IsEtale B S hS (f p) ∧
        CompactSpace ((BigFppfOver.toScheme B S hS).obj (V p)) ∧
        Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj (V p)) ∧
        ((BigFppfOver.toScheme B S hS).obj (V p)).size ≤
          max ℵ₀ ((BigFppfOver.toScheme B S hS).obj A).size ∧
        IsQuasiCompactSpace B S hS (U p.val).toFunctor := by
  classical
  obtain ⟨n, U, -, hUzero, hUn, hUopen, hUnested, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace B S hS hZ X hX hqc hqs
  refine ⟨n, U, V, f, hUzero, hUn,
    by rw [hUn]; exact nonempty_sheafify_bot_iso_initialObj B S hS X hX,
    hUopen, hUnested, fun i => ?_⟩
  obtain ⟨hTclosed, hTsupport, hTred, hVcompact, hVsep, hsurj, hf, hpb⟩ := hdata i
  have hp : i.val < n := i.isLt
  have hUp := hUopen i.val hp.le
  have hsq := isElementaryDistinguishedSquare_of_reducedStratum B S hS hX
    (isAlgebraicSpace_yoneda B S hS (V i)) (U (i.val + 1)) (U i.val) (hUopen (i.val + 1) hp)
    hUp (hUnested i.val hp) (T i) hTclosed hTsupport hTred (f i) hf hpb
  rw [range_homOfLe_eq_preimage] at hsq
  have hsize : ((BigFppfOver.toScheme B S hS).obj (V i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj A).size :=
    size_le_of_isEtale_of_atlas B S hS haSurj haEtale
      (isEtale_comp B S hS hf (isEtale_of_isOpenImmersion B S hS hUp.2))
  exact ⟨⟨hUp.1, hsq⟩, hsurj, hf, hVcompact, hVsep, le_max_of_le_right hsize,
    ⟨V i, f i, hVcompact, hsurj, hf⟩⟩

end AlgebraicGeometry.Space

end
