module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.CategoryTheory.Sites.SubfunctorCoproductOfSheafifySup

/-!
# Zariski's main theorem for a separated morphism of finite type of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is of finite type and
separated, and let `X --f'--> Y' --ν--> Y` be the normalization of `Y` in `X`. Tag 082I says
that there is an open subspace `U' ⊆ Y'` such that

1. `(f')⁻¹(U') ⟶ U'` is an isomorphism, and
2. `(f')⁻¹(U') ⊆ X` is the set of points at which `f` is quasi-finite.

This file proves it, for `f` not assumed representable, following the source's proof.

## Main results

* `IsRelativeNormalization.isOpenImmersion_and_isPullback_of_isIntegralHom`
  (in `AlgebraicGeometry.Space`): if the source of `f : X ⟶ T` decomposes as `V ⨿ W`, with `W` a
  closed subspace and `V ⟶ T` integral, then `V` maps by an open immersion into the normalization
  `Y'` of `T` in `X`, and `V = V ×_{Y'} X`. This is the step "the normalization of `Y` in
  `X = V ⨿ W` is `V ⨿ W'`" of the source (Tags 0824, 0825 and 0414).
* `AlgebraicGeometry.Space.IsRelativeNormalization.exists_isEtale_isPullback_of_isQuasiFiniteAt`:
  the claim of the source's proof, in the form used for the descent: around the image in `Y'`
  of a point of quasi-finiteness there is an étale morphism `q : Q ⟶ Y'` over which `f'` is an
  isomorphism and whose source maps into the quasi-finite locus.
* `exists_isOpenSubspace_isIso_fromPreimage_and_range_pointsMap_preimage_eq`
  (in `AlgebraicGeometry.Space.IsRelativeNormalization`): **Tag 082I**, for every factorization
  of `f` with the universal property of Tag 0823.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isIso_fromPreimage_toNormalizationInQcqs`:
  **Tag 082I** at the normalization of Definition 0822.

## Implementation notes

**The normalization.** The source writes "let `Y'` be the normalization of `Y` in `X`". The
normalization of Definition 0822 is `AlgebraicGeometry.Space.normalizationInQcqs`, which exists
because `f`, being of finite type and separated, is quasi-compact and quasi-separated; by
Tag 0823 it is characterized, up to unique isomorphism, by the predicate
`AlgebraicGeometry.Space.IsRelativeNormalization`. The main theorem is stated for every
factorization satisfying that predicate, which is the stronger form, and is then specialized to
the constructed normalization.

**The proof.** It is the source's. For a point `x` at which `f` is quasi-finite, Tag 0ADU gives an
étale `U ⟶ Y` and a decomposition `U ×_Y X = V ⨿ W` into open and closed subspaces with `V ⟶ U`
finite and `x` in the image of `V`. The base change `U ×_Y Y'` is the normalization of `U` in
`U ×_Y X` (Tag 082F, an étale morphism being smooth), and that normalization is `V ⨿ W'` with `W'`
the normalization of `U` in `W` (Tags 0824, 0825, 0414); so `V ⟶ U ×_Y Y'` is an open immersion
over which the base change of `f'` is an isomorphism, and `V ⟶ U ×_Y Y' ⟶ Y'` is étale. The open
subspace `U'` is the image of the quasi-finite locus, which is the union of the images of these
étale morphisms and hence open (Tag 03IR). The identification of `(f')⁻¹(U')` with the quasi-finite
locus uses that quasi-finiteness at a point is insensitive to base change (Tag 04NW), and the
isomorphism `(f')⁻¹(U') ⟶ U'` is descended along the étale covering of `U'` by the `V`'s, being an
isomorphism being fpqc local on the base (Tag 041Y).

The decomposition `U ×_Y X = V ⨿ W` of Tag 0ADU is a pair of subfunctors which locally cover and
are locally disjoint; it is turned into a coproduct of sheaves, the form Tag 0824 consumes, by
`CategoryTheory.Subfunctor.isColimitCofanOfSheafifySup`. That `V = V ×_{Y'} X` is then the
disjointness of finite coproducts of sheaves of sets, i.e. extensivity of the topos.

## References

* [Stacks Project, Tag 082I](https://stacks.math.columbia.edu/tag/082I)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 082F](https://stacks.math.columbia.edu/tag/082F)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0824](https://stacks.math.columbia.edu/tag/0824)
* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

namespace IsRelativeNormalization

/-- **The normalization of a disjoint union with an integral piece.** Let `f : X ⟶ T` be a
quasi-compact and quasi-separated morphism of algebraic spaces over `S` with normalization
`X ⟶ Y' ⟶ T`, and let `X = V ⨿ W` be a decomposition into subfunctors which locally cover `X`
and are locally disjoint, with `V` an algebraic space, `W` a closed subspace and `V ⟶ T`
integral. Then
`V ⟶ X ⟶ Y'` is an open immersion and the square `V = V ×_{Y'} X` is cartesian, so that `f'`
is an isomorphism over the image of `V`.

The normalization of `T` in `V ⨿ W` is `V ⨿ W'`, with `W'` the normalization of `T` in `W`: by
Tag 0824, by Tag 0825 for the integral piece, and by Definition 0822 for `W`, which exists
because `W ⟶ T` is quasi-compact and quasi-separated. -/
theorem isOpenImmersion_and_isPullback_of_isIntegralHom
    {X T Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ T} {ν : Y' ⟶ T} {f' : X ⟶ Y'}
    (h : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hT : IsAlgebraicSpace B S hS T)
    (hY' : IsAlgebraicSpace B S hS Y')
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (V W : Subfunctor X) (hV : IsAlgebraicSpace B S hS V.toFunctor)
    (hWc : IsClosedSubspace B S hS W)
    (hsup : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hinf : W ⊓ V = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS))
    (hVint : IsIntegralHom B S hS (V.ι ≫ f)) :
    IsOpenImmersion B S hS (V.ι ≫ f') ∧ IsPullback V.ι (𝟙 V.toFunctor) f' (V.ι ≫ f') := by
  classical
  have := BigFppfOver.hasSheafify_type B S hS
  have hVW : ∀ b : Bool, IsAlgebraicSpace B S hS (cond b V W).toFunctor := fun b => by
    cases b
    exacts [hWc.1, hV]
  have hXc := Subfunctor.isColimitCofanOfSheafifySup (J := BigFppfOver.topology B S hS)
    (V := V) (W := W) hX.isSheaf (fun b => (hVW b).isSheaf)
    (by rwa [sup_comm]) (by rw [inf_comm, hinf])
  -- the normalization of `T` in `W`
  let Ws : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWc.1⟩
  let Ts : AlgebraicSpaces B S hS := ⟨T, hT⟩
  let fWs : Ws ⟶ Ts := ObjectProperty.homMk (W.ι ≫ f)
  have hWqc : IsQuasiCompact B S hS (W.ι ≫ f) :=
    isQuasiCompact_comp B S hS hX hT W.ι f
      (isQuasiCompact_of_isClosedImmersion B S hS W.ι hWc.1 hX hWc.2) hqc
  have hWqs : IsQuasiSeparated B S hS (W.ι ≫ f) :=
    isQuasiSeparated_comp B S hS hWc.1 hX W.ι f
      (isQuasiSeparated_of_isClosedImmersion B S hS hWc.2) hqs
  let NW := normalizationInQcqs B S hS fWs hWqc hWqs
  let N : Bool → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun b => cond b V.toFunctor NW.1
  have hN : ∀ b, IsAlgebraicSpace B S hS (N b) := fun b => by
    cases b
    exacts [NW.2, hV]
  let νs : ∀ b, N b ⟶ T := fun b => match b with
    | true => V.ι ≫ f
    | false => (normalizationInQcqsHom B S hS fWs hWqc hWqs).hom
  let fs : ∀ b, (cond b V W).toFunctor ⟶ N b := fun b => match b with
    | true => 𝟙 _
    | false => (toNormalizationInQcqs fWs hWqc hWqs).hom
  have hnorm : ∀ b, IsRelativeNormalization B S hS ((cond b V W).ι ≫ f) (νs b) (fs b) := by
    intro b
    cases b
    · exact isRelativeNormalization_normalizationInQcqs fWs hWqc hWqs
    · exact isRelativeNormalization_id_of_isIntegralHom hVint
  let Ns : Bool → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun b => ⟨N b, (hN b).isSheaf⟩
  have : HasColimit (Discrete.functor Ns) :=
    HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩
  let P := ∐ Ns
  have hP : IsColimit (Cofan.mk P (Sigma.ι Ns)) := coproductIsCoproduct Ns
  have hPalg : IsAlgebraicSpace B S hS P.obj :=
    isAlgebraicSpace_finiteCoproduct B S hS N hN P (Sigma.ι Ns) hP
  let νP : P.obj ⟶ T :=
    (Sigma.desc (fun b => (ObjectProperty.homMk (νs b) : Ns b ⟶ ⟨T, hT.isSheaf⟩))).hom
  have hν : ∀ b, (Sigma.ι Ns b).hom ≫ νP = νs b := fun b =>
    Sheaf.hom_ext_iff.1 (Sigma.ι_comp_desc _ b)
  let f'' : X ⟶ P.obj :=
    (Cofan.IsColimit.desc hXc (fun b => ObjectProperty.homMk (fs b) ≫ Sigma.ι Ns b)).hom
  have hf' : ∀ b, (cond b V W).ι ≫ f'' = fs b ≫ (Sigma.ι Ns b).hom := fun b =>
    Sheaf.hom_ext_iff.1 (Cofan.IsColimit.fac hXc _ b)
  have h0824 := isRelativeNormalization_coproduct B S hS hT
    (fun b => (cond b V W).toFunctor) hVW ⟨X, hX.isSheaf⟩
    (fun b => ObjectProperty.homMk (cond b V W).ι) hXc f N hN νs fs hnorm P (Sigma.ι Ns) hP
    νP hν f'' hf'
  obtain ⟨e, ⟨he, -⟩, -⟩ := h0824.existsUnique_iso h hPalg hY'
  have hVf' : V.ι ≫ f' = (Sigma.ι Ns true).hom ≫ e.hom := by
    rw [← he, ← Category.assoc]
    exact congrArg (· ≫ e.hom) ((hf' true).trans (Category.id_comp _))
  have hoi : IsOpenImmersion B S hS (V.ι ≫ f') := by
    rw [hVf']
    exact isOpenImmersion_comp B S hS _ _
      (coproductIncl_isOpenImmersion B S hS Ns P (Sigma.ι Ns) hP true)
      (isOpenImmersion_of_isIso B S hS e.hom)
  refine ⟨hoi, ?_⟩
  let α : Discrete.functor (fun b => (⟨(cond b V W).toFunctor, (hVW b).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u))) ⟶ Discrete.functor Ns :=
    Discrete.natTrans fun b => ObjectProperty.homMk (fs b.as)
  have hcomm : α ≫ (Cofan.mk P (Sigma.ι Ns)).ι =
      (Cofan.mk (⟨X, hX.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u))
        (fun b => ObjectProperty.homMk (cond b V W).ι)).ι ≫
        (Functor.const _).map (ObjectProperty.homMk f'') := by
    refine NatTrans.ext (funext fun b => ?_)
    obtain ⟨b⟩ := b
    exact (Cofan.IsColimit.fac hXc (fun b => ObjectProperty.homMk (fs b) ≫ Sigma.ι Ns b) b).symm
  have hpb := ((FinitaryExtensive.isVanKampen_finiteCoproducts hP) _ α
    (ObjectProperty.homMk f'') hcomm (NatTrans.Equifibered.of_discrete _)).1 ⟨hXc⟩ ⟨true⟩
  have hpb' : IsPullback V.ι (𝟙 V.toFunctor) f'' (Sigma.ι Ns true).hom :=
    hpb.map (sheafToPresheaf _ _)
  exact IsPullback.of_iso hpb' (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
    (by simpa using he) (by simpa using hVf'.symm)

/-- **The claim of the proof of Tag 082I.** Let `f : X ⟶ Y` be of finite type and separated,
with normalization `X ⟶ Y' ⟶ Y`, and let `x` be a point at which `f` is quasi-finite. Then
there is an étale morphism `q : Q ⟶ Y'` of algebraic spaces whose image contains `f'(x)`, over
which `f'` is an isomorphism (the square `Q = Q ×_{Y'} X` is cartesian), and such that `f` is
quasi-finite at every point of `X` in the image of `Q`.

The space `Q` is the finite piece `V` of an étale neighbourhood `U ×_Y X = V ⨿ W` of `x`
(Tag 0ADU), mapped to `Y'` through the normalization `U ×_Y Y'` of `U` in `U ×_Y X`
(Tag 082F). -/
theorem exists_isEtale_isPullback_of_isQuasiFiniteAt
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {ν : Y' ⟶ Y} {f' : X ⟶ Y'}
    (h : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (hft : IsFiniteType B S hS f)
    (hsep : IsSeparated B S hS f) (x : points B S hS X) (hx : IsQuasiFiniteAt B S hS f x) :
    ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Q) (q : Q ⟶ Y')
      (a : Q ⟶ X), IsEtale B S hS q ∧ IsPullback a (𝟙 Q) f' q ∧
        pointsMap B S hS X f' x ∈ Set.range (pointsMap B S hS Q q) ∧
        ∀ z, IsQuasiFiniteAt B S hS f (pointsMap B S hS Q a z) := by
  obtain ⟨U, g, u, W, V, hgE, -, -, hWc, hVo, -, hsup, hinf, hVfin, v, hvx, -⟩ :=
    exists_etale_decomposition_isFinite_point_of_isQuasiFiniteAt B S hS hX hY f x _ rfl hft.1
      hsep hx
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hXU : IsAlgebraicSpace B S hS (pullback g f) := isAlgebraicSpace_pullback B S hS g f hU hX hY
  have hY'U : IsAlgebraicSpace B S hS (pullback ν g) :=
    isAlgebraicSpace_pullback B S hS ν g hY' hU hY
  have hnU := h.isRelativeNormalization_baseChange_of_isSmooth hY hU hX hY' hft.2
    (isQuasiSeparated_of_isSeparated B S hS hsep) (isSmooth_of_isEtale B S hS hY hgE)
    (IsPullback.of_hasPullback g f).flip (IsPullback.of_hasPullback ν g).flip
  set f'U := h.baseChangeFactorization (IsPullback.of_hasPullback g f).flip
    (IsPullback.of_hasPullback ν g).flip
  have hfUqc : IsQuasiCompact B S hS (pullback.fst g f) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hft.2
  have hfUqs : IsQuasiSeparated B S hS (pullback.fst g f) :=
    isQuasiSeparated_of_isSeparated B S hS (isSeparated_pullbackFst B S hS g hsep)
  obtain ⟨hoi, hpb⟩ := hnU.isOpenImmersion_and_isPullback_of_isIntegralHom hXU hU hY'U hfUqc
    hfUqs V W hVo.1 hWc hsup hinf (IsFinite.isIntegralHom B S hS hVfin)
  have hsq : IsPullback (pullback.snd g f) f'U f' (pullback.fst ν g) := by
    refine IsPullback.of_bot ?_ (h.baseChangeFactorization_snd _ _).symm
      (IsPullback.of_hasPullback ν g)
    rw [h.baseChangeFactorization_fst, h.fac]
    exact (IsPullback.of_hasPullback g f).flip
  have hlqf : IsLocallyQuasiFinite B S hS (V.ι ≫ pullback.fst g f) :=
    (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hVo.1 hU _ hVfin).2
  let Y'Us : AlgebraicSpaces B S hS := ⟨pullback ν g, hY'U⟩
  let Us : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hU⟩
  have hprE : IsEtale B S hS (pullback.fst ν g) :=
    isEtale_of_isPullback B S hS (ObjectProperty.homMk (pullback.snd ν g) : Y'Us ⟶ Us)
      (ObjectProperty.homMk (pullback.fst ν g) : Y'Us ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk g : Us ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk ν : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (IsPullback.of_map_of_faithful (F := ObjectProperty.ι (IsAlgebraicSpace B S hS))
        (IsPullback.of_hasPullback ν g).flip) hgE
  refine ⟨V.toFunctor, hVo.1, (V.ι ≫ f'U) ≫ pullback.fst ν g, V.ι ≫ pullback.snd g f,
    isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hoi) hprE,
    hpb.paste_horiz hsq, ⟨v, ?_⟩, fun z => ?_⟩
  · rw [← hvx, ← pointsMap_comp_apply, (hpb.paste_horiz hsq).w, Category.id_comp]
  · rw [pointsMap_comp_apply]
    exact (isQuasiFiniteAt_iff_of_isPullback B S hS (IsPullback.of_hasPullback g f) hX hY hU
      hft.1 _).1 ⟨V, hVo, z, rfl, hlqf⟩

/-- **Stacks 082I.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is of
finite type and separated, and let `ν : Y' ⟶ Y`, `f' : X ⟶ Y'` be the normalization of `Y` in
`X`, in the sense of the characterization of Tag 0823. Then there is an open subspace
`U' ⊆ Y'` such that `(f')⁻¹(U') ⟶ U'` is an isomorphism and the point set of `(f')⁻¹(U')` is
the set of points of `X` at which `f` is quasi-finite.

The open subspace is the image of the quasi-finite locus. It is covered by the étale
morphisms of `IsRelativeNormalization.exists_isEtale_isPullback_of_isQuasiFiniteAt`, one for
each point of quasi-finiteness, which makes it open and identifies its inverse image;
and `(f')⁻¹(U') ⟶ U'` is an isomorphism after base change to each of them, hence an
isomorphism by Tag 041Y. -/
@[stacks 082I "both numbered conclusions, for every factorization of f with the universal \
property of Tag 0823 (the normalization of Y in X)"]
theorem exists_isOpenSubspace_isIso_fromPreimage_and_range_pointsMap_preimage_eq
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {ν : Y' ⟶ Y} {f' : X ⟶ Y'}
    (h : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (hft : IsFiniteType B S hS f)
    (hsep : IsSeparated B S hS f) :
    ∃ U' : Subfunctor Y', IsOpenSubspace B S hS U' ∧ IsIso (U'.fromPreimage f') ∧
      Set.range (pointsMap B S hS (U'.preimage f').toFunctor (U'.preimage f').ι) =
        {x : points B S hS X | IsQuasiFiniteAt B S hS f x} := by
  let I := {x : points B S hS X // IsQuasiFiniteAt B S hS f x}
  choose Q hQ q a hqet hpb hmem hqf using fun i : I =>
    h.exists_isEtale_isPullback_of_isQuasiFiniteAt hX hY hY' hft hsep i.1 i.2
  let Uset : Set (points B S hS Y') :=
    pointsMap B S hS X f' '' {x | IsQuasiFiniteAt B S hS f x}
  have hrange : ∀ i z, pointsMap B S hS (Q i) (q i) z ∈ Uset := fun i z =>
    ⟨pointsMap B S hS (Q i) (a i) z, hqf i z, by
      rw [← pointsMap_comp_apply, (hpb i).w, Category.id_comp]⟩
  have hex : ∀ p ∈ Uset, ∃ i z, pointsMap B S hS (Q i) (q i) z = p := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have hopen : IsOpen Uset := by
    rw [show Uset = ⋃ i, Set.range (pointsMap B S hS (Q i) (q i)) from
      Set.Subset.antisymm (fun p hp => by simpa using hex p hp)
        (Set.iUnion_subset fun i => by rintro _ ⟨z, rfl⟩; exact hrange i z)]
    refine isOpen_iUnion fun i => ?_
    rw [← Set.image_univ]
    exact isOpenMap_pointsMap_of_isEtale B S hS (q i) (hQ i) hY' (hqet i) _ isOpen_univ
  let U' := openSubspaceOfPoints B S hS Y' Uset
  have hU' : IsOpenSubspace B S hS U' := isOpenSubspace_openSubspaceOfPoints B S hS hY' Uset hopen
  have hU'pts : Set.range (pointsMap B S hS U'.toFunctor U'.ι) = Uset :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Uset
  have hpts : Set.range (pointsMap B S hS (U'.preimage f').toFunctor (U'.preimage f').ι) =
      {x : points B S hS X | IsQuasiFiniteAt B S hS f x} := by
    rw [pointsRange_preimage, hU'pts]
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ⟨x, hx, rfl⟩)
    obtain ⟨i, z, hz⟩ := hex _ hx
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (hpb i) x z hz.symm
    rw [← hw]
    exact hqf i w
  refine ⟨U', hU', ?_, hpts⟩
  -- the étale morphisms factor through `U'`
  have hle : ∀ i, Subfunctor.range (q i) ≤ U' := by
    rintro i T _ ⟨y, rfl⟩
    rw [mem_openSubspaceOfPoints_iff, ← yonedaEquiv_symm_naturality_right, pointsMap_comp]
    rintro _ ⟨t, rfl⟩
    exact hrange i _
  let q' : ∀ i, Q i ⟶ U'.toFunctor := fun i => Subfunctor.lift (q i) (hle i)
  have hq' : ∀ i, q' i ≫ U'.ι = q i := fun i => Subfunctor.lift_ι _ _
  have hlea : ∀ i, Subfunctor.range (a i) ≤ U'.preimage f' := by
    rintro i T _ ⟨y, rfl⟩
    change f'.app T ((a i).app T y) ∈ U'.obj T
    rw [← NatTrans.comp_app_apply, (hpb i).w, Category.id_comp]
    exact hle i T ⟨y, rfl⟩
  let a' : ∀ i, Q i ⟶ (U'.preimage f').toFunctor := fun i => Subfunctor.lift (a i) (hlea i)
  have hpb' : ∀ i, IsPullback (a' i) (𝟙 (Q i)) (U'.fromPreimage f') (q' i) := fun i => by
    refine IsPullback.of_right (h₁₂ := (U'.preimage f').ι) (h₂₂ := U'.ι) ?_ ?_
      (Subfunctor.isPullback_preimage f' U').flip
    · rw [Subfunctor.lift_ι, hq']
      exact hpb i
    · rw [← cancel_mono U'.ι, Category.assoc, Subfunctor.fromPreimage_ι, Category.id_comp, hq',
        ← Category.assoc, Subfunctor.lift_ι]
      exact (hpb i).w.trans (Category.id_comp _)
  -- descend the isomorphism along the étale covering `{q' i}`
  have hpre : IsAlgebraicSpace B S hS (U'.preimage f').toFunctor :=
    (isOpenSubspace_preimage B S hS f' U' hY' hX hU').1
  let Fs : (⟨(U'.preimage f').toFunctor, hpre⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U'.toFunctor, hU'.1⟩ :=
    ObjectProperty.homMk (U'.fromPreimage f')
  have hcov : IsEtaleCovering B S hS Q q' := by
    refine ⟨hU'.1, hQ, fun i => isEtale_of_comp_mono B S hS (q' i) U'.ι (by rw [hq']; exact hqet i),
      Set.eq_univ_of_forall fun p => ?_⟩
    have hp : pointsMap B S hS U'.toFunctor U'.ι p ∈ Uset := hU'pts ▸ ⟨p, rfl⟩
    obtain ⟨i, z, hz⟩ := hex _ hp
    obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS (IsKernelPair.id_of_mono U'.ι)
      p (pointsMap B S hS (Q i) (q' i) z) (by rw [← pointsMap_comp_apply, hq', hz])
    rw [pointsMap_id, id_eq] at hw₁ hw₂
    exact Set.mem_iUnion.2 ⟨i, z, hw₂.symm.trans hw₁⟩
  let Qs : I → AlgebraicSpaces B S hS := fun i => ⟨Q i, hQ i⟩
  have hR : Presieve.ofArrows Qs (fun i => (ObjectProperty.homMk (q' i) : Qs i ⟶
        ⟨U'.toFunctor, hU'.1⟩)) ∈ Topology.precoverage .fpqc B S hS ⟨U'.toFunctor, hU'.1⟩ :=
    ⟨I, _, _, rfl, hU'.1, hQ, isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov⟩
  have hFs : IsIso Fs := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)) hR ?_
    rintro Z g _ ⟨i⟩
    have hpbs := IsPullback.of_map_of_faithful (F := ObjectProperty.ι (IsAlgebraicSpace B S hS))
      (f := (ObjectProperty.homMk (a' i) : Qs i ⟶ ⟨(U'.preimage f').toFunctor, hpre⟩))
      (g := 𝟙 (Qs i)) (h := Fs)
      (i := (ObjectProperty.homMk (q' i) : Qs i ⟶ ⟨U'.toFunctor, hU'.1⟩)) (hpb' i)
    have : IsIso (hpbs.isoPullback.hom ≫ pullback.snd Fs _) := by
      rw [hpbs.isoPullback_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left hpbs.isoPullback.hom _
  exact (ObjectProperty.isIso_hom_iff Fs).2 hFs

end IsRelativeNormalization

/-- **Stacks 082I, at the normalization of Definition 0822.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is of finite type and separated, and let `X ⟶ Y' ⟶ Y` be the
normalization of `Y` in `X` constructed in Definition 0822 (it exists since `f` is
quasi-compact and quasi-separated). Then there is an open subspace `U' ⊆ Y'` such that
`(f')⁻¹(U') ⟶ U'` is an isomorphism and the point set of `(f')⁻¹(U')` is the set of points of
`X` at which `f` is quasi-finite. -/
@[stacks 082I "both numbered conclusions, at the normalization of Y in X constructed in \
Definition 0822"]
theorem exists_isOpenSubspace_isIso_fromPreimage_toNormalizationInQcqs
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hft : IsFiniteType B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) :
    ∃ U' : Subfunctor (normalizationInQcqs B S hS f hft.2
        (isQuasiSeparated_of_isSeparated B S hS hsep)).obj,
      IsOpenSubspace B S hS U' ∧
      IsIso (U'.fromPreimage (toNormalizationInQcqs f hft.2
        (isQuasiSeparated_of_isSeparated B S hS hsep)).hom) ∧
      Set.range (pointsMap B S hS (U'.preimage (toNormalizationInQcqs f hft.2
          (isQuasiSeparated_of_isSeparated B S hS hsep)).hom).toFunctor
          (U'.preimage (toNormalizationInQcqs f hft.2
            (isQuasiSeparated_of_isSeparated B S hS hsep)).hom).ι) =
        {x : points B S hS X.obj | IsQuasiFiniteAt B S hS f.hom x} :=
  IsRelativeNormalization.exists_isOpenSubspace_isIso_fromPreimage_and_range_pointsMap_preimage_eq
    (isRelativeNormalization_normalizationInQcqs f hft.2
      (isQuasiSeparated_of_isSeparated B S hS hsep))
    X.property Y.property (normalizationInQcqs B S hS f _ _).property hft hsep

end AlgebraicGeometry.Space

end
