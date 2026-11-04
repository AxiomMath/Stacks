module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek

/-!
# Base change of an extension by zero, and constructibility on a scheme that is only
quasi-separated

Let `g : T ⟶ S` be a morphism of a big étale site and let `U` be an object of the small étale site
of `S`. Inverse image along `g` carries `j_{U!}\underline{\Lambda}_U` to
`j_{U_T!}\underline{\Lambda}_{U_T}`, where `U_T = U ×_S T` is the small étale base change of `U`:
extension by zero of a constant module sheaf commutes with base change. This is
`AlgebraicGeometry.moduleShriekConstantSheafPullbackIso`, and no hypothesis on `g` is needed; the
coefficient ring `Λ : Type r` lies in a universe of its own, the sheaves of modules in
`ModuleCat.{max (u + 1) r} Λ`.

The consequence drawn here is that **quasi-compactness of the ambient scheme is not needed** in
Stacks 03S8 nor in its flat refinement. Constructibility is a condition on each affine open, so
it may be checked on an open covering (Stacks 095F,
`AlgebraicGeometry.isStratifiedSheaf_of_openCover_of_immersionStable`); on an affine member `W` of
such a covering the base change isomorphism replaces the restriction of
`j_{U!}\underline{\Lambda}_U` by `j_{U_W!}\underline{\Lambda}_{U_W}`, and `W` is quasi-compact and
quasi-separated, so the existing statements apply to it. What `U_W` must still be is quasi-compact
and quasi-separated, and that is where quasi-separatedness of the ambient scheme enters and stays:
`U_W` is quasi-compact because `U ⟶ S` is a quasi-compact morphism, which for `U` quasi-compact is
exactly quasi-separatedness of `S` (`AlgebraicGeometry.quasiCompact_of_compactSpace`).

## Main results

* `AlgebraicGeometry.moduleShriekConstantSheafPullbackIso` — **extension by zero of a constant
  module sheaf commutes with base change**, along an arbitrary morphism of the big étale site and
  for a ring in a universe of its own.
* `AlgebraicGeometry.compactSpace_smallEtaleBaseChange` and
  `AlgebraicGeometry.quasiSeparatedSpace_smallEtaleBaseChange` — the base change of a
  quasi-compact quasi-separated étale object along a morphism from a quasi-compact
  quasi-separated scheme is again quasi-compact and quasi-separated, the first granted
  quasi-separatedness of the target.
* `AlgebraicGeometry.exists_affine_openCover_of_bigEtaleSite` — the affine open cover of a scheme
  of the site, presented inside the site.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_openCover` — **flat constructibility is
  Zariski local**, for an arbitrary ring in an arbitrary module universe and with no hypothesis
  on the scheme.
* `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_quasiSeparated`,
  `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant_of_quasiSeparated` and
  `AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant_of_quasiSeparated` —
  **Stacks 03S8, its module form and its flat refinement, with the ambient scheme only
  quasi-separated**, the module statements for a ring in a universe of its own, and
  `AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated`
  for a finite direct sum at affine objects.

## Implementation notes

No `@[stacks 03S8]` attribute is attached to the generalizations: the tag is already registered on
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` and on
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, which these statements are
proved *from*, at the affine members of a covering. They weaken a hypothesis of the tagged
statements rather than proving new content of the tag.

The base change isomorphism is assembled from three comparisons already available and does not
unfold either extension by zero: `AlgebraicGeometry.moduleShriekConstantIsoCopower` rewrites
`j_{U!}\underline{\Lambda}_U` as the copower module sheaf, by the free rank-one module, on the
sheaf of sets `h_U^#`, `CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso`
commutes the copower module sheaf past inverse image, and
`Stacks.Sites.sheafPullbackSheafifiedUliftYonedaIso` — Stacks 04D3 for sheafified representables
at the module universe — identifies the inverse image of `h_U^#` with `h_{U_T}^#`.

The ring universe is free because none of the three mentions `ModuleCat.free Λ`, which carries
the ring and the module in one universe. Routing instead through `ModuleCat.copower`, whose ring
universe is free, is what releases it; the copower takes sheaves of sets in the *module* universe,
which is why the sheafified representable is `CategoryTheory.Sheaf.sheafifiedUliftYoneda` rather
than `CategoryTheory.Sheaf.sheafifiedYoneda`. Commutativity of `Λ` is a different matter and is
not released: `AlgebraicGeometry.moduleShriekConstant` is stated for a commutative ring.

Universes are written out at every application, as they are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekConstantCopower`.
`AlgebraicGeometry.moduleShriekConstant` has a third universe parameter which the module universe
`max (u + 1) r` pins down only through a `max`, so leaving it to inference would let a statement
be about a universe nobody wrote; the annotations say which statement is meant, and are not a
workaround for a failure of elaboration.

Quasi-separatedness of the ambient scheme cannot be dropped as well, and the statements above are
sharp in that respect. Glue two copies of `X = Spec k[x_1, x_2, …]` along the open subscheme
`V = X \ {(x_1, x_2, …)}`, which is not quasi-compact, to get a scheme `Y` that is not
quasi-separated; let `U` be one of the two copies, an affine object of the small étale site of `Y`
through an open immersion. On the other copy, an affine open of `Y`, the sheaf
`j_{U!}\underline{\Lambda}_U` has stalk `Λ` at the points of `V` and `0` elsewhere, so on a
stratum of a stratification witnessing constructibility the subset `V` would have to be open and
closed, hence `V` would be a finite union of constructible sets and so constructible — which an
open set that is not quasi-compact is not. So `j_{U!}\underline{\Lambda}_U` is not a constructible
sheaf on `Y` for `Λ ≠ 0`.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w r

namespace AlgebraicGeometry

section BaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Extension by zero of a constant module sheaf commutes with base change.** For an arbitrary
morphism `g : T ⟶ S` of the big étale site and an object `U` of the small étale site of `S`, the
inverse image along `g` of `j_{U!}\underline{\Lambda}_U` is `j_{U_T!}\underline{\Lambda}_{U_T}`,
where `U_T = (smallEtaleBaseChange B g).obj U` is the fibre product `U ×_S T`. The ring is in a
universe of its own.

Both sides are the copower module sheaf on a sheafified representable, by
`AlgebraicGeometry.moduleShriekConstantIsoCopower`; the copower module sheaf commutes with
inverse image, and the inverse image of `h_U^#` is `h_{U_T}^#`. -/
public def moduleShriekConstantSheafPullbackIso {S T : B.Scheme} (g : T ⟶ S)
    (U : SmallEtale B S.obj S.property) :
    ((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj
      (moduleShriekConstant.{u, r, r} B S Λ U) ≅
      moduleShriekConstant.{u, r, r} B T Λ ((smallEtaleBaseChange B g).obj U) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B S Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, r} B T Λ
  exact ((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).mapIso
        (moduleShriekConstantIsoCopower B S Λ U) ≪≫
    (Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso
      (SmallEtale.topology B S.obj S.property)
      (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))
      (SmallEtale.topology B T.obj T.property) (smallEtaleBaseChange B g)).app
        ((Sheaf.sheafifiedUliftYoneda.{r} (SmallEtale.topology B S.obj S.property)).obj U) ≪≫
    (Sheaf.composeAndSheafify (SmallEtale.topology B T.obj T.property)
      (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))).mapIso
        (Stacks.Sites.sheafPullbackSheafifiedUliftYonedaIso.{r} (smallEtaleBaseChange B g)
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) U) ≪≫
    (moduleShriekConstantIsoCopower B T Λ ((smallEtaleBaseChange B g).obj U)).symm

end BaseChange

section Geometry

variable (B : BigEtaleSite.{u})

/-- The square exhibiting the small étale base change of `U` along `g : T ⟶ S` as a fibre
product of schemes. -/
public theorem isPullback_smallEtaleBaseChange {S T : B.Scheme} (g : T ⟶ S)
    (U : SmallEtale B S.obj S.property) :
    IsPullback (B.inclusion.map (Limits.pullback.fst U.obj.hom g))
      (B.inclusion.map (Limits.pullback.snd U.obj.hom g))
      (B.inclusion.map U.obj.hom) (B.inclusion.map g) :=
  (IsPullback.of_hasPullback U.obj.hom g).map B.inclusion

/-- **The base change of a quasi-compact étale object along a morphism from a quasi-compact
scheme is quasi-compact**, provided the target is quasi-separated. The structure morphism of `U`
is a quasi-compact morphism, a morphism from a quasi-compact scheme to a quasi-separated one being
quasi-compact, and quasi-compactness of a morphism is stable under base change; the base change of
`U` is the second projection of the fibre product.

Quasi-separatedness of `S` is what is really used, and it cannot be dropped: the preimage of an
affine open of a non-quasi-separated scheme under an open immersion from an affine scheme need not
be quasi-compact. -/
public theorem compactSpace_smallEtaleBaseChange {S T : B.Scheme} (g : T ⟶ S)
    (U : SmallEtale B S.obj S.property) [QuasiSeparatedSpace S.obj]
    [CompactSpace T.obj] [CompactSpace U.obj.left.obj] :
    CompactSpace ((smallEtaleBaseChange B g).obj U).obj.left.obj := by
  have hSq : QuasiSeparatedSpace (B.inclusion.obj S) := ‹QuasiSeparatedSpace S.obj›
  have hTc : CompactSpace (B.inclusion.obj T) := ‹CompactSpace T.obj›
  have hUc : CompactSpace (B.inclusion.obj U.obj.left) := ‹CompactSpace U.obj.left.obj›
  have hqc : QuasiCompact (B.inclusion.map (Limits.pullback.snd U.obj.hom g)) :=
    MorphismProperty.of_isPullback (isPullback_smallEtaleBaseChange B g U)
      (inferInstance : QuasiCompact (B.inclusion.map U.obj.hom))
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hqc hTc

/-- **The base change of a quasi-separated étale object along a morphism from a quasi-separated
scheme is quasi-separated.** The structure morphism of `U` is a quasi-separated morphism, its
source being a quasi-separated scheme, and that property is stable under base change. -/
public theorem quasiSeparatedSpace_smallEtaleBaseChange {S T : B.Scheme} (g : T ⟶ S)
    (U : SmallEtale B S.obj S.property) [QuasiSeparatedSpace T.obj]
    [QuasiSeparatedSpace U.obj.left.obj] :
    QuasiSeparatedSpace ((smallEtaleBaseChange B g).obj U).obj.left.obj := by
  have hTq : QuasiSeparatedSpace (B.inclusion.obj T) := ‹QuasiSeparatedSpace T.obj›
  have hUq : QuasiSeparatedSpace (B.inclusion.obj U.obj.left) :=
    ‹QuasiSeparatedSpace U.obj.left.obj›
  have hqs : QuasiSeparated (B.inclusion.map (Limits.pullback.snd U.obj.hom g)) :=
    MorphismProperty.of_isPullback (isPullback_smallEtaleBaseChange B g U)
      (inferInstance : QuasiSeparated (B.inclusion.map U.obj.hom))
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ _ hTq hqs

/-- The base change of a quasi-compact quasi-separated étale object of a quasi-separated scheme
along a morphism from an affine scheme is quasi-compact and quasi-separated. -/
private theorem compact_quasiSeparated_smallEtaleBaseChange_of_isAffine {S T : B.Scheme}
    (g : T ⟶ S) (U : SmallEtale B S.obj S.property) [QuasiSeparatedSpace S.obj]
    [IsAffine T.obj] [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    CompactSpace ((smallEtaleBaseChange B g).obj U).obj.left.obj ∧
      QuasiSeparatedSpace ((smallEtaleBaseChange B g).obj U).obj.left.obj :=
  ⟨compactSpace_smallEtaleBaseChange B g U, quasiSeparatedSpace_smallEtaleBaseChange B g U⟩

/-- **The affine opens of a scheme of the big étale site cover it inside the site.** Each member
of the affine open cover of `X` is again an object of `B`, its size being bounded by that of `X`,
and the inclusions are open immersions whose images cover `X`. -/
public theorem exists_affine_openCover_of_bigEtaleSite (X : B.Scheme) :
    ∃ (I : Type u) (W : I → B.Scheme) (j : ∀ k, W k ⟶ X),
      (∀ k, IsOpenImmersion (B.inclusion.map (j k))) ∧
      (∀ k, IsAffine (W k).obj) ∧
      Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base := by
  have hopen : ∀ i, IsOpenImmersion ((B.inclusion.obj X).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj X).affineOpenCover.openCover.map_prop i
  have hmem : ∀ i, B.Contains ((B.inclusion.obj X).affineOpenCover.openCover.X i) := by
    intro i
    have := hopen i
    exact Scheme.size_lt_of_isOpenImmersion
      ((B.inclusion.obj X).affineOpenCover.openCover.f i) X.property
  exact ⟨(B.inclusion.obj X).affineOpenCover.openCover.I₀,
    fun i => B.obj ((B.inclusion.obj X).affineOpenCover.openCover.X i) (hmem i),
    fun i => ObjectProperty.homMk ((B.inclusion.obj X).affineOpenCover.openCover.f i),
    fun i => hopen i, fun i => Scheme.isAffine_affineCover (B.inclusion.obj X) i,
    ((B.inclusion.obj X).affineOpenCover.openCover.iUnion_range).symm⟩

end Geometry

section FlatDescent

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- **Flat constructibility is Zariski local.** A sheaf of `Λ`-modules whose inverse image on
every member of an open covering of `X` is constructible flat is constructible flat. No hypothesis
on `X` is needed, and the ring and the module universe are free.

This is `AlgebraicGeometry.isStratifiedSheaf_of_openCover_of_immersionStable`, Stacks 095F for an
arbitrary condition on the strata, at local constancy with finite projective values; its two
inputs are `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr` and
`AlgebraicGeometry.isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback`, the latter holding
along an arbitrary morphism, so the hypothesis that the morphism is an immersion is discarded. -/
public theorem isConstructibleFlatModuleSheaf_of_openCover (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    {I : Type*} (W : I → B.Scheme) (j : ∀ k, W k ⟶ X)
    (hj : ∀ k, IsOpenImmersion (B.inclusion.map (j k)))
    (hcover : Set.univ = ⋃ k, Set.range (B.inclusion.map (j k)).base)
    (hlocal : ∀ k, IsConstructibleFlatModuleSheaf B (W k) Λ
      (((smallEtaleBaseChange B (j k)).sheafPullback (ModuleCat.{w} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (W k).obj (W k).property)).obj F)) :
    IsConstructibleFlatModuleSheaf B X Λ F := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G := by
    intro _ _ _ e h
    exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ e h
  have hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ),
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T'.obj T'.property)
        (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{w} Λ)
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G) := fun _ _ g _ G h =>
    isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ g G h
  exact isStratifiedSheaf_of_openCover_of_immersionStable B X _ hPIso hPImmersion F W j hj
    hcover hlocal

end FlatDescent

section Shriek

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

/-- **The flat refinement of Stacks 03S8 with the ambient scheme only quasi-separated.** For `U`
a quasi-compact quasi-separated object of the small étale site of a *quasi-separated* scheme `X`,
and `Λ` a commutative ring in an arbitrary universe `r`, the extension by zero
`j_{U!}\underline{\Lambda}_U` of the constant free rank-one module sheaf is a flat constructible
sheaf of `Λ`-modules in `ModuleCat.{max (u + 1) r} Λ`.

Flat constructibility is Zariski local, the affine opens of `X` cover it, and on an affine open
`W` the restriction of `j_{U!}\underline{\Lambda}_U` is `j_{U_W!}\underline{\Lambda}_{U_W}` by
`AlgebraicGeometry.moduleShriekConstantSheafPullbackIso`; `W` is quasi-compact and
quasi-separated, and so is `U_W`, so
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant` applies there. -/
public theorem isConstructibleFlatModuleSheaf_moduleShriekConstant_of_quasiSeparated
    [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleFlatModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) := by
  obtain ⟨I, W, j, hj, hWaff, hcover⟩ := exists_affine_openCover_of_bigEtaleSite B X
  refine isConstructibleFlatModuleSheaf_of_openCover B Λ X _ W j hj hcover fun i => ?_
  have hA : IsAffine (W i).obj := hWaff i
  obtain ⟨hbc, hbq⟩ := compact_quasiSeparated_smallEtaleBaseChange_of_isAffine B (j i) U
  exact isConstructibleFlatModuleSheaf_congr B (W i) Λ
    (moduleShriekConstantSheafPullbackIso B Λ (j i) U).symm
    (isConstructibleFlatModuleSheaf_moduleShriekConstant B (W i) Λ
      ((smallEtaleBaseChange B (j i)).obj U))

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **A finite direct sum of extensions by zero of constant free rank-one module sheaves at
affine objects is flat constructible, the ambient scheme being only quasi-separated.** This is
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant` with
quasi-compactness of `X` removed; the summands are handled by
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant_of_quasiSeparated` and
assembled by `AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma`. -/
public theorem isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated
    [QuasiSeparatedSpace X.obj] {n : ℕ} (U : Fin n → SmallEtale B X.obj X.property)
    (hU : ∀ j, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j))) :
    IsConstructibleFlatModuleSheaf B X Λ
      (∐ fun j => moduleShriekConstant.{u, r, r} B X Λ (U j)) := by
  have : ∀ T : B.Scheme,
      HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ) :=
    fun T => SmallEtale.hasSheafify_moduleCat.{u, r, r} B T Λ
  refine isConstructibleFlatModuleSheaf_sigma B X Λ _ fun j => ?_
  have hA : IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j)) := hU j
  have hc : CompactSpace (U j).obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U j)))
  have hq : QuasiSeparatedSpace (U j).obj.left.obj :=
    inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U j)))
  exact isConstructibleFlatModuleSheaf_moduleShriekConstant_of_quasiSeparated B X Λ (U j)

variable [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- **Stacks 03S8 for sheaves of modules with the ambient scheme only quasi-separated.** Over a
Noetherian commutative ring a finite projective module is finitely generated, so this is the flat
refinement read through
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`. -/
public theorem isConstructibleModuleSheaf_moduleShriekConstant_of_quasiSeparated
    [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) :=
  isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ
    (isConstructibleFlatModuleSheaf_moduleShriekConstant_of_quasiSeparated B X Λ U)

end Shriek

section Sets

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Stacks 03S8 part (1) with the ambient scheme only quasi-separated.** For `U` a quasi-compact
quasi-separated object of the small étale site of a *quasi-separated* scheme `X`, the sheaf `h_U`
represented by `U` is a constructible sheaf of sets on `X_étale`.

Constructibility of a sheaf of sets is Zariski local by Stacks 095F,
`AlgebraicGeometry.isConstructibleFiniteSheaf_of_openCover`, and on an affine open `W` of `X` the
inverse image of `h_U^#` is `h_{U_W}^#` by `Stacks.Sites.sheafPullbackSheafifiedYonedaIso`, so
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` applies there. -/
public theorem isConstructibleSetSheaf_sheafifiedYoneda_of_quasiSeparated
    [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) := by
  obtain ⟨I, W, j, hj, hWaff, hcover⟩ := exists_affine_openCover_of_bigEtaleSite B X
  refine isConstructibleFiniteSheaf_of_openCover B X _ W j hj hcover fun i => ?_
  have hA : IsAffine (W i).obj := hWaff i
  obtain ⟨hbc, hbq⟩ := compact_quasiSeparated_smallEtaleBaseChange_of_isAffine B (j i) U
  refine isStratifiedSheaf_congr B (W i)
    (fun T H => Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B T.obj T.property) H) ?_
    (Stacks.Sites.sheafPullbackSheafifiedYonedaIso (smallEtaleBaseChange B (j i))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (W i).obj (W i).property) U).symm
    (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B (W i)
      ((smallEtaleBaseChange B (j i)).obj U))
  intro T F G e h
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
    (SmallEtale.topology B T.obj T.property) e (hF := h)

end Sets

end AlgebraicGeometry

end
