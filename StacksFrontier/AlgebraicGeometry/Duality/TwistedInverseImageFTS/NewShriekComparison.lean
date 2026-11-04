module

public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexes
public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekPseudoFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionComposition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexNegativeExt
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `f_new^!` is `f^!` for a separated morphism

In Situation [Stacks, Tag 0AU4], let `ω_X^•` and `ω_Y^•` be the dualizing complexes normalized
relative to `ω_S^•` and let `f : X ⟶ Y` be a separated morphism of schemes of finite type over
`S`. The closing remark of [Stacks, Tag 0AUE] gives a canonical isomorphism

`f_new^! M ≅ f^! M`, `M ∈ D^+_Coh(𝒪_Y)`,

where `f_new^! = D_X ∘ Lf^* ∘ D_Y` (`Stacks.Duality.fNewShriekStd`). The proof is the source's:
`ω_X^• ≅ f^! ω_Y^•` (`Stacks.Duality.NormalizedOnOpens.upperShriekObjIso`), and [Stacks, Tag 0AU2]
for `f` over the base `Y`, `f^! M ≅ R𝓗om(Lf^* D_Y(M), f^! ω_Y^•)`.

`f^!` is the upper shriek functor of the compactification `c f hf`, the one
`Stacks.Duality.UpperShriek.ofCompactifications c` uses; it is read at the standard model, where
`f_new^!` lives, by `Stacks.Duality.UpperShriekDuality.upperShriekStd`.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.stdComplex` — `ω_X^•` read at the standard model.
* `Stacks.Duality.NormalizedOnOpens.stdComplexRestrictIso` — for an open `V ⊆ X`, the normalized
  complex `ω_X^•|_V` is `L(V → X)^* ω_X^•` at the standard model.
* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekOfIso` — `f^! ≅ f_new^!` through
  any identification `f^!K ≅ ω`.
* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriek` — `f^! ≅ f_new^!` on
  `D^+_Coh(𝒪_Y)`, for `f` separated.
* `Stacks.Duality.NormalizedOnOpens.coherentDuality_spec_stdComplex` — part (3) of
  [Stacks, Tag 0AUE]: `D_X = R𝓗om(-, ω_X^•)` is an involution of `D_Coh(𝒪_X)` exchanging
  `D^+_Coh` and `D^-_Coh` and fixing `D^b_Coh`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom pull comparison plusCoh IsDualizing
  stdMonoidal stdSymmetric stdMonoidalClosed)
open CategoryTheory.MonoidalClosed (dualInto)

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- The normalized complex `ω_X^•`, read at the standard model of `D(𝒪_X)`. -/
abbrev stdComplex (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) : Std X :=
  (comparison X).inverse.obj 𝒦.complex.obj.obj

/-- **The normalized complex of an open is the restriction**: for an open `V ⊆ X`,
`ω_X^•|_V = (V → X)^! ω_X^•` is `L(V → X)^* ω_X^•`, read at the standard model, since
`j^! = Lj^*` for an open immersion `j` ([Stacks, Tag 0AU0]). -/
def stdComplexRestrictIso (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (V : X.Opens) :
    stdComplex c (𝒦.restrict V) ≅ (pull V.ι).obj (stdComplex c 𝒦) :=
  (comparison V).inverse.mapIso ((ObjectProperty.ι _).mapIso
      ((UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion c V.ι (hp.isShriekable_ι V)).app
        𝒦.complex)) ≪≫
    (UpperShriekDuality.pullModelConj V.ι).app _

include hpe in
/-- The normalized complex is dualizing at the standard model. -/
theorem isDualizing_stdComplex
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) :
    haveI := hp.source_noetherian
    IsDualizing (stdComplex c 𝒦) :=
  have := hp.source_noetherian
  isDualizingComplex_standard_of_isDualizingComplex
    (𝒦.isDualizingComplex_ofCompactifications c hωS)

/-- `f` as a morphism of `FTS_Y`, with the target as base. -/
abbrev ftsHomSelf (hf : IsShriekable f) :=
  ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f)

/-- The dualizing complex `ω_Y^•` of `D^+_QCoh` read back from its standard-model form. -/
def dualizingQCohIso (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    [AlgebraicGeometry.IsNoetherian Y] (hK : IsDualizing (stdComplex c 𝒦Y)) :
    UpperShriekDuality.dualizingQCoh (S := Y) (Y := ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y))
        hK ≅ 𝒦Y.complex.obj :=
  ObjectProperty.isoMk _ ((comparison Y).counitIso.app 𝒦Y.complex.obj.obj)

/-- **The duality formula of [Stacks, Tag 0AU2] read as `f^! ≅ f_new^!`**: for a separated
`f : X ⟶ Y`, a compactification `j`, a dualizing complex `K` on `Y` and an identification
`e : f^!K ≅ ω` with a complex `ω` on `X`, `f^!M ≅ R𝓗om(Lf^* D_Y(M), ω) = f_new^!M` naturally in
`M ∈ D^+_Coh(𝒪_Y)`, where `f_new^!` is formed with `ω_X^• = ω` and `ω_Y^• = K`. -/
def upperShriekStdIsoFNewShriekOfIso {T : Scheme.{u}} [AlgebraicGeometry.IsNoetherian T]
    {A B : FTS T} (g : A ⟶ B) (j : CompactificationOf (Over.mk g.left)) {K : Std B.left}
    (hK : IsDualizing K) {ω : Std A.left}
    (e : UpperShriekDuality.upperShriekDualizing g j hK ≅ ω) :
    UpperShriekDuality.upperShriekStd g j ≅ (plusCoh B.left).ι ⋙ fNewShriekStd g.left ω K :=
  UpperShriekDuality.upperShriekDualityIso g j hK ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      ((sheafHom A.left).flip.mapIso e ≪≫ (relativeDualIsoSheafHom _).symm))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (natIsoRightOp (relativeDualIsoSheafHom K).symm) _)

/-- **The closing remark of [Stacks, Tag 0AUE], second half**, for the upper shriek functors of
compactifications: for a separated morphism `f : X ⟶ Y` of schemes of finite type over `S` and
the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•`, there is a canonical
isomorphism `f^! M ≅ f_new^! M = D_X(Lf^* D_Y(M))`, natural in `M ∈ D^+_Coh(𝒪_Y)`. -/
def upperShriekStdIsoFNewShriek
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    UpperShriekDuality.upperShriekStd (ftsHomSelf hf) (c f hf) ≅
      (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex c 𝒦X) (stdComplex c 𝒦Y) :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  let hK := isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y
  upperShriekStdIsoFNewShriekOfIso (ftsHomSelf hf) (c f hf) hK
    ((comparison X).inverse.mapIso
      ((ObjectProperty.ι _).mapIso ((upperShriek (ftsHomSelf hf) (c f hf)).mapIso
          (dualizingQCohIso c 𝒦Y hK)) ≪≫
        (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso
          (upperShriekObjIso c hpe hωS hf 𝒦X 𝒦Y).symm)))

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed in
/-- **[Stacks, Tag 0AUE] part (3).** For `X` of finite type over the base and `ω_X^•` normalized
relative to `ω_S^•`, the duality `D_X = R𝓗om(-, ω_X^•)` carries `D_Coh(𝒪_X)` into itself and is
an anti-equivalence of it with `id ≅ D_X ∘ D_X` given by biduality; it exchanges `D^+_Coh` and
`D^-_Coh` and is an anti-equivalence of `D^b_Coh(𝒪_X)`. This is [Stacks, Tag 0A89] for the
dualizing complex `ω_X^•`. -/
theorem coherentDuality_spec_stdComplex
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) :
    haveI := hp.source_noetherian
    cohStd X (stdComplex c 𝒦) ∧
    (∀ M : Std X, cohStd X M → cohStd X ((dualInto (stdComplex c 𝒦)).obj (op M))) ∧
    (coherentDuality X (isDualizing_stdComplex c (Category.id_comp p) hωS 𝒦)).IsEquivalence ∧
    IsIso (coherentBiduality X (isDualizing_stdComplex c (Category.id_comp p) hωS 𝒦)) ∧
    (∀ M : Std X, cohStd X M →
      (plusCoh X M ↔ minusCoh X ((dualInto (stdComplex c 𝒦)).obj (op M))) ∧
        (minusCoh X M ↔ plusCoh X ((dualInto (stdComplex c 𝒦)).obj (op M)))) ∧
    (boundedCoherentDuality X
      (isDualizing_stdComplex c (Category.id_comp p) hωS 𝒦)).IsEquivalence := by
  have := hp.source_noetherian
  have hK := isDualizing_stdComplex c (Category.id_comp p) hωS 𝒦
  obtain ⟨h1, -, h3, h4, h5⟩ := coherentDuality_spec X hK
  exact ⟨h1, fun M hM i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hM i,
    h3, h4, fun M hM => plusCoh_iff_minusCoh_dual hK M hM, h5.2⟩

end NormalizedOnOpens

end Stacks.Duality

end
