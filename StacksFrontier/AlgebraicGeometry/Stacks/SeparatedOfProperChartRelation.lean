module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent

/-!
# Separatedness of a 1-morphism read off a chart

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `x : 𝒰 ⟶ 𝒳` be a
1-morphism representable by algebraic spaces which is surjective, flat and locally of finite
presentation, for instance a smooth surjective chart of `𝒳` by an algebraic space. Write
`R = 𝒰 ×_𝒳 𝒰` for the relation of the chart and

```text
  (s, t) : 𝒰 ×_𝒳 𝒰 ⟶ 𝒰 ×_𝒴 𝒰
```

for the comparison 1-morphism of Stacks 050H. Then `f` is separated if and only if `(s, t)` is
proper. This is the step "`𝒳 → Y` is separated if `R → U ×_Y U` is proper, because
`U ×_Y U → 𝒳 ×_Y 𝒳` is surjective and smooth" that the proofs of Stacks 0CPZ and Stacks 0CQ2
take from Properties of Stacks, Lemma 04XD.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.localEssSurj_mapCospan`: if `x` is locally essentially
  surjective, so is `x × x : 𝒰 ×_𝒴 𝒰 ⟶ 𝒳 ×_𝒴 𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isProper_mapBase`: properness of
  `(s, t)` gives separatedness of `f`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_iff_isProper_mapBase`: the equivalence.

## Implementation notes

By Stacks 050H (`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_mapBaseSquare`) the
comparison 1-morphism `(s, t)` is the base change of the relative diagonal `Δ_f` along
`x × x : 𝒰 ×_𝒴 𝒰 ⟶ 𝒳 ×_𝒴 𝒳` (`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan`). Properness
descends along that base change by Stacks 045D
(`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`), whose hypothesis is the local
essential surjectivity of `x × x`; this is the form in which Stacks 04XD is applied to the
diagonal in the separated case of Stacks 06TZ.

The local essential surjectivity of `x × x` is proved directly. An object of `𝒳 ×_𝒴 𝒳` over `U`
is a pair `(a, b)` of objects of `𝒳` over `U` with a vertical isomorphism `f a ≅ f b`. Locally on
`U` both `a` and `b` are images under `x` of objects `z₁`, `z₂` of `𝒰`, by morphisms
`ψ₁ : x z₁ ⟶ a` and `ψ₂ : x z₂ ⟶ b`. Since `𝒴` is fibred in groupoids, `f ψ₂` is cartesian, so
the composite of `f ψ₁` with the given isomorphism factors uniquely through it by a vertical
isomorphism `f (x z₁) ≅ f (x z₂)`; this is the comparison isomorphism of the required object of
`𝒰 ×_𝒴 𝒰`, and `(ψ₁, ψ₂)` is the required morphism.

## References

* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 0CPZ](https://stacks.math.columbia.edu/tag/0CPZ)
* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **`x × x` is locally essentially surjective when `x` is.** For 1-morphisms `x : 𝒰 ⟶ 𝒳` and
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, if every object of a fibre of `𝒳` becomes isomorphic
to an image under `x` after restriction to a covering sieve, then every object of a fibre of
`𝒳 ×_𝒴 𝒳` becomes isomorphic to an image under `x × x : 𝒰 ×_𝒴 𝒰 ⟶ 𝒳 ×_𝒴 𝒳` after restriction
to a covering sieve. -/
theorem localEssSurj_mapCospan (x : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hx : ∀ (U : BigFppfOver B S hS) (t : 𝒳.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒰.val.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor x.hom).obj z ⟶ t.1,
            𝒳.val.val.p.IsHomLift k φ) :
    ∀ (U : BigFppfOver B S hS) (t : (twoFibreProduct B S hS f f).val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : (twoFibreProduct B S hS (x ≫ f) (x ≫ f)).val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor (mapCospan B S hS x x f).hom).obj z ⟶ t.1,
              (twoFibreProduct B S hS f f).val.val.p.IsHomLift k φ := by
  rintro U ⟨T, rfl⟩
  obtain ⟨R₁, hR₁, h₁⟩ := hx _ ⟨T.x, T.hx⟩
  obtain ⟨R₂, hR₂, h₂⟩ := hx _ ⟨T.y, T.hy⟩
  refine ⟨R₁ ⊓ R₂, (BigFppfOver.topology B S hS).intersection_covering hR₁ hR₂, fun V k hk => ?_⟩
  obtain ⟨z₁, ψ₁, hψ₁⟩ := h₁ hk.1
  obtain ⟨z₂, ψ₂, hψ₂⟩ := h₂ hk.2
  -- the two lifts lie over `V`, because `x` is a 1-morphism over the site
  have hz : ∀ {z a} (ψ : (CatFiberedInGroupoids.homFunctor x.hom).obj z ⟶ a),
      𝒳.val.val.p.IsHomLift k ψ → 𝒰.val.val.p.obj z = V := fun ψ hψ =>
    (Functor.congr_obj x.hom.hom.w _).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p k ψ)
  -- the vertical comparison isomorphism `f (x z₁) ≅ f (x z₂)`, through the cartesian `f ψ₂`
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hφ : ∀ {a b : 𝒳.val.val.obj} (ψ : a ⟶ b), 𝒳.val.val.p.IsHomLift k ψ →
      𝒴.val.val.p.IsHomLift k (F.map ψ) := fun ψ _ =>
    Functor.isHomLift_map_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p f.hom) k ψ
  have := hφ ψ₁ hψ₁
  have := hφ ψ₂ hψ₂
  have hvert : 𝒴.val.val.p.IsHomLift (𝟙 ((twoFibreProduct B S hS f f).val.val.p.obj T))
      T.iso.hom := T.vertical
  have hφ' : 𝒴.val.val.p.IsHomLift k (F.map ψ₁ ≫ T.iso.hom) := inferInstance
  have hp := CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val
  have := hp.isStronglyCartesian_homLift k (F.map ψ₂)
  have := hp.isStronglyCartesian_homLift k (F.map ψ₁ ≫ T.iso.hom)
  let ι := Functor.IsCartesian.domainUniqueUpToIso 𝒴.val.val.p k (F.map ψ₂)
    (F.map ψ₁ ≫ T.iso.hom)
  have hι : 𝒴.val.val.p.IsHomLift (𝟙 V) ι.hom := inferInstance
  have hιw : ι.hom ≫ F.map ψ₂ = F.map ψ₁ ≫ T.iso.hom :=
    Functor.IsCartesian.fac 𝒴.val.val.p k (F.map ψ₂) (F.map ψ₁ ≫ T.iso.hom)
  exact ⟨⟨V, z₁, z₂, hz _ hψ₁, hz _ hψ₂, ι, hι⟩,
    { hbase := k, a := ψ₁, b := ψ₂, ha := hψ₁, hb := hψ₂, w := hιw.symm },
    structureFunctor_isHomLift _ k hψ₁⟩

/-- **Separatedness from a chart.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S` and let `x : 𝒰 ⟶ 𝒳` be representable by algebraic spaces, surjective, flat and locally of
finite presentation. If the comparison 1-morphism `(s, t) : 𝒰 ×_𝒳 𝒰 ⟶ 𝒰 ×_𝒴 𝒰` is proper, then
`f` is separated.

The square of Stacks 050H exhibits `(s, t)` as the base change of `Δ_f` along
`x × x : 𝒰 ×_𝒴 𝒰 ⟶ 𝒳 ×_𝒴 𝒳`, and properness descends along it by Stacks 045D, `x × x` being
locally essentially surjective by `localEssSurj_mapCospan`. -/
theorem isSeparated_of_isProper_mapBase (f : 𝒳 ⟶ 𝒴) (x : 𝒰 ⟶ 𝒳)
    (hxr : IsRepresentableByAlgebraicSpaces B S hS x.hom.hom)
    (hxSurj : Stack.IsSurjective B S hS x) (hxFlat : IsFlat B S hS x)
    (hxLfp : IsLocallyOfFinitePresentation B S hS x)
    (h : Stack.IsProper.{u, u, u + 1} B S hS (mapBase B S hS x x f).hom) :
    IsSeparated B S hS f := by
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  -- `x` is locally essentially surjective, being surjective, flat and locally of finite
  -- presentation in the relative sense of Stacks 03YK
  have hxLES := Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS
    x.hom hxr (fun U y hy F hF he =>
      ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS x hxr).1
          hxSurj U y hy F hF he,
        (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒰.property 𝒳.property
          x.hom hxr).1 hxFlat U y hy F hF he,
        (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
          𝒰.property 𝒳.property x.hom hxr).1
            ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
              (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
              𝒰.property 𝒳.property x.hom).1 hxLfp) U y hy F hF he⟩)
  have hprBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hprLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  exact hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS 𝒳.val
    (twoFibreProduct B S hS f f).val (twoFibreProduct B S hS (x ≫ f) (x ≫ f)).val
    (fun _ _ k => Space.IsProper B S hS k.hom)
    (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
    (mapCospan B S hS x x f).hom (mapBaseSquare B S hS x x f)
    (isTwoFibreProduct_mapBaseSquare B S hS x x f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (localEssSurj_mapCospan B S hS x f hxLES) h

/-- **Separatedness is read off a chart.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks
over `S` and let `x : 𝒰 ⟶ 𝒳` be representable by algebraic spaces, surjective, flat and locally
of finite presentation. Then `f` is separated if and only if the comparison 1-morphism
`(s, t) : 𝒰 ×_𝒳 𝒰 ⟶ 𝒰 ×_𝒴 𝒰` is proper. The forward implication is part (6) of Stacks 050H and
uses no hypothesis on `x`. -/
theorem isSeparated_iff_isProper_mapBase (f : 𝒳 ⟶ 𝒴) (x : 𝒰 ⟶ 𝒳)
    (hxr : IsRepresentableByAlgebraicSpaces B S hS x.hom.hom)
    (hxSurj : Stack.IsSurjective B S hS x) (hxFlat : IsFlat B S hS x)
    (hxLfp : IsLocallyOfFinitePresentation B S hS x) :
    IsSeparated B S hS f ↔ Stack.IsProper.{u, u, u + 1} B S hS (mapBase B S hS x x f).hom :=
  ⟨isProper_mapBase_of_isSeparated B S hS x x f,
    isSeparated_of_isProper_mapBase B S hS f x hxr hxSurj hxFlat hxLfp⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
