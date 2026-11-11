module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.MayerVietorisShortExact

/-!
# The Mayer--Vietoris distinguished triangle on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` and an open covering `X = X' ∪ X''`, with
`X''' = X' ∩ X''`.  `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.openCoverShortComplex_shortExact` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisShortExact.lean` says that at a
*fixed* object `(U, T, δ)` of `Cris(X/S)` the Mayer--Vietoris sequence

`0 ⟶ I(U, T, δ) ⟶ I' ⊕ I'' ⟶ I''' ⟶ 0`

of an injective abelian sheaf is short exact.  Those three assignments are functorial in the
sheaf, so they assemble into a short complex of additive functors
`Ab(Cris(X/S)) ⥤ Ab` which is short exact at every injective object — exactly the hypothesis of
`CategoryTheory.triangleOfInjectiveCochainComplex_distinguished` and of
`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives` of
`StacksFrontier/Algebra/Homology/DerivedFunctorLongExact.lean`.  Feeding it to them produces, for
every cochain complex `K` of injective abelian sheaves on `Cris(X/S)`, a distinguished triangle

`Γ((U, T, δ), K) ⟶ Γ((U', T', δ'), K) ⊕ Γ((U'', T'', δ''), K) ⟶ Γ((U''', T''', δ'''), K) ⟶ [1]`

in `D(Ab)`, and a long exact sequence of the right derived functors of the three section
functors.

## Main definitions

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`.

* `biprodObjIso` — a biproduct of two functors into abelian groups, evaluated at an object, is
  the biproduct of the two evaluations.
* `sectionsFunctor` — the functor `F ↦ F(U, T, δ)` of sections of an abelian sheaf on
  `Cris(X/S)` at a fixed object of the site.
* `openCoverFunctorComplex` — the Mayer--Vietoris short complex of section functors of a pair of
  opens of `X` at an object of `Cris(X/S)`, a short complex in the abelian functor category
  `Ab(Cris(X/S)) ⥤ Ab`.
* `openCoverAppComplex` — its value at a sheaf, as a short complex of abelian groups.
* `openCoverAppComplexIso` — the comparison of that value with `openCoverShortComplex`.
* `openCoverTriangle` — **the Mayer--Vietoris triangle of the covering at a cochain complex of
  injective abelian sheaves**, in the derived category of abelian groups.

## Main results

* `shortExact_openCoverAppComplex` — the short complex of section functors is short exact at
  every injective abelian sheaf.
* `openCoverTriangle_distinguished` — the Mayer--Vietoris triangle at a fixed object is
  distinguished.  Its three terms are read off by `openCoverTriangle_obj₁`,
  `openCoverTriangle_obj₂` and `openCoverTriangle_obj₃`.
* `longExact_openCoverFunctorComplex` — the long exact sequence of right derived functors of the
  three section functors.

## Relation to [Stacks, Tag 07ML]

What is proved here is a triangle **at a fixed object `(U, T, δ)` of `Cris(X/S)` and a fixed pair
of opens of `X`**: its three terms are the sections of a complex of injective abelian sheaves over
`(U, T, δ)` and over its three restrictions.  It is a local, object-level relative of the remark,
not the remark.  The remark of [Stacks, Tag 07ML] is a distinguished triangle of the derived
direct images `Rf_{cris, *}F`, `Rf'_{cris, *}F' ⊕ Rf''_{cris, *}F''`, `Rf'''_{cris, *}F'''` in
`D(𝒪_{X'/S'})`, for `f : X ⟶ X'` in the situation of [Stacks, Tag 07MJ]; it is proved as
`...SmallSite.exists_distinguished_triangle_derivedCrisModuleDirectImage` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisDirectImage.lean`, which
carries the Stacks attribute for tag 07ML.  That proof does not go through the section functors of
this file: it uses the sheaf-level Mayer--Vietoris sequence of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisSequence.lean` and the
identification of the direct image along `f|_V` with that along `f` of `j_{V, *}` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisModuleDirectImageOpenSubspace.lean`.

The complex `K` is required to consist of injective sheaves, which is what the general machinery
of `StacksFrontier/Algebra/Homology/DerivedFunctorLongExact.lean` consumes.

## Implementation notes

The middle term of `openCoverFunctorComplex` is the binary biproduct of two section functors
taken in the functor category `Ab(Cris(X/S)) ⥤ Ab`, which is abelian because `AddCommGrpCat` is.
Evaluating a biproduct of functors at a sheaf is only *canonically*, not definitionally, the
biproduct of the evaluations, so `openCoverAppComplexIso` is not `Iso.refl`: its middle component
is `biprodObjIso`, the pair of evaluated projections.  That is the only discrepancy between
`openCoverAppComplex` and `openCoverShortComplex`; the outer two components are `Iso.refl`.

`biprodObjIso` is written out by hand rather than obtained from
`CategoryTheory.Functor.mapBiprod` for the evaluation functor.  The latter would do — evaluation
is additive, hence preserves binary biproducts — but it brings its own
`CategoryTheory.Limits.HasBinaryBiproduct` instance for the evaluated pair, spelled through
`CategoryTheory.sheafSections` rather than through the sections of the sheaf, and the resulting
mismatch of spellings blocks `CategoryTheory.Limits.biprod.lift_fst`.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  Opposite

universe w u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}}

/-- **Evaluating a biproduct of functors into abelian groups at an object is the biproduct of
the two evaluations.**  Both sides have the universal property of the biproduct of the two
evaluations; the comparison is the pair of evaluated projections. -/
@[simps]
def biprodObjIso (Φ Ψ : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (Φ ⊞ Ψ).obj F ≅ Φ.obj F ⊞ Ψ.obj F where
  hom := biprod.lift ((biprod.fst : Φ ⊞ Ψ ⟶ Φ).app F) ((biprod.snd : Φ ⊞ Ψ ⟶ Ψ).app F)
  inv := biprod.desc ((biprod.inl : Φ ⟶ Φ ⊞ Ψ).app F) ((biprod.inr : Ψ ⟶ Φ ⊞ Ψ).app F)
  hom_inv_id := by
    rw [biprod.lift_desc, ← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.app_add,
      biprod.total, NatTrans.id_app]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.lift_fst, biprod.lift_snd, Category.comp_id,
        ← NatTrans.comp_app, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        NatTrans.id_app, NatTrans.app_zero]

/-- **The functor of sections at an object `(U, T, δ)` of `Cris(X/S)`**, sending an abelian sheaf
`F` on the small crystalline site to the abelian group `F(U, T, δ)`. -/
abbrev sectionsFunctor (A : CrystallineThickening S) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections (smallTopology S) AddCommGrpCat.{u + 1}).obj (op A)

/-- The value of the sections functor at a sheaf is the group of sections of that sheaf. -/
@[simp]
theorem sectionsFunctor_obj (A : CrystallineThickening S)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (sectionsFunctor A).obj F = F.obj.obj (op A) :=
  rfl

/-- Sections at an object of `Cris(X/S)` are an additive functor: addition of morphisms of
abelian sheaves is componentwise. -/
instance instAdditiveSectionsFunctor (A : CrystallineThickening S) :
    (sectionsFunctor A).Additive where
  map_add := rfl

/-- **Restriction of sections along a morphism of `Cris(X/S)`**, as a natural transformation of
section functors. -/
abbrev sectionsFunctorMap {A B : CrystallineThickening S} (f : A ⟶ B) :
    sectionsFunctor B ⟶ sectionsFunctor A :=
  (sheafSections (smallTopology S) AddCommGrpCat.{u + 1}).map f.op

/-- Restriction of sections at a sheaf is the restriction map of that sheaf. -/
@[simp]
theorem sectionsFunctorMap_app {A B : CrystallineThickening S} (f : A ⟶ B)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (sectionsFunctorMap f).app F = F.obj.map f.op :=
  rfl

/-- **The Mayer--Vietoris short complex of section functors of an open covering `X = X' ∪ X''` at
an object `(U, T, δ)` of `Cris(X/S)`**: sections over `(U, T, δ)`, then the biproduct of sections
over the restrictions to `X'` and `X''`, then sections over the restriction to
`X''' = X' ∩ X''`, with the difference of the two restriction maps as its second arrow.  This is
`openCoverShortComplex` made functorial in the sheaf. -/
def openCoverFunctorComplex (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    ShortComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk
    (biprod.lift (sectionsFunctorMap (openCoverSquare A V₁ V₂).f₂₄)
      (sectionsFunctorMap (openCoverSquare A V₁ V₂).f₃₄))
    (biprod.desc (sectionsFunctorMap (openCoverSquare A V₁ V₂).f₁₂)
      (-sectionsFunctorMap (openCoverSquare A V₁ V₂).f₁₃))
    (by simp [← Functor.map_comp, ← op_comp, (openCoverSquare A V₁ V₂).fac])

/-- The first term of the Mayer--Vietoris short complex of section functors is additive. -/
instance instAdditiveOpenCoverFunctorComplexX₁ (A : CrystallineThickening S)
    (V₁ V₂ : S.X.Opens) : (openCoverFunctorComplex A V₁ V₂).X₁.Additive :=
  inferInstanceAs (sectionsFunctor (openCoverSquare A V₁ V₂).X₄).Additive

/-- The middle term of the Mayer--Vietoris short complex of section functors is additive. -/
instance instAdditiveOpenCoverFunctorComplexX₂ (A : CrystallineThickening S)
    (V₁ V₂ : S.X.Opens) : (openCoverFunctorComplex A V₁ V₂).X₂.Additive :=
  inferInstanceAs (sectionsFunctor (openCoverSquare A V₁ V₂).X₂ ⊞
    sectionsFunctor (openCoverSquare A V₁ V₂).X₃).Additive

/-- The last term of the Mayer--Vietoris short complex of section functors is additive. -/
instance instAdditiveOpenCoverFunctorComplexX₃ (A : CrystallineThickening S)
    (V₁ V₂ : S.X.Opens) : (openCoverFunctorComplex A V₁ V₂).X₃.Additive :=
  inferInstanceAs (sectionsFunctor (openCoverSquare A V₁ V₂).X₁).Additive

/-- The value of the Mayer--Vietoris short complex of section functors at an abelian sheaf `F`,
as a short complex of abelian groups. -/
abbrev openCoverAppComplex (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : ShortComplex AddCommGrpCat.{u + 1} :=
  NatTrans.appShortComplex (openCoverFunctorComplex A V₁ V₂).f
    (openCoverFunctorComplex A V₁ V₂).g (openCoverFunctorComplex A V₁ V₂).zero F

/-- **The value of the Mayer--Vietoris short complex of section functors at a sheaf `F` is the
Mayer--Vietoris short complex of `F`.**  The outer terms agree on the nose; in the middle, the
biproduct of two functors evaluated at `F` is compared with the biproduct of their values by
`biprodObjIso`. -/
def openCoverAppComplexIso (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    openCoverAppComplex A V₁ V₂ F ≅ openCoverShortComplex A V₁ V₂ F :=
  ShortComplex.isoMk (Iso.refl _)
    (biprodObjIso (sectionsFunctor (openCoverSquare A V₁ V₂).X₂)
      (sectionsFunctor (openCoverSquare A V₁ V₂).X₃) F)
    (Iso.refl _)
    (by
      dsimp only [openCoverAppComplex, openCoverShortComplex, openCoverFunctorComplex,
        Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex,
        NatTrans.appShortComplex]
      apply biprod.hom_ext
      all_goals
        simp only [Iso.refl_hom, Category.id_comp, Category.assoc, biprodObjIso_hom]
        dsimp only [sectionsFunctor_obj]
        simp only [biprod.lift_fst, biprod.lift_snd, ← NatTrans.comp_app,
          sectionsFunctorMap_app])
    (by
      dsimp only [openCoverAppComplex, openCoverShortComplex, openCoverFunctorComplex,
        Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex,
        NatTrans.appShortComplex]
      rw [Iso.refl_hom, Category.comp_id, ← Iso.eq_inv_comp]
      apply biprod.hom_ext' <;>
        simp only [biprodObjIso_inv, biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc,
          biprod.inr_desc_assoc, ← NatTrans.comp_app, NatTrans.app_neg, sectionsFunctorMap_app])

/-- **The Mayer--Vietoris short complex of section functors of an open covering `X = X' ∪ X''` is
short exact at every injective abelian sheaf.**  This is
`openCoverShortComplex_shortExact` transported along `openCoverAppComplexIso`, and it is the
hypothesis the derived machinery of `StacksFrontier/Algebra/Homology/DerivedFunctorLongExact.lean`
consumes. -/
theorem shortExact_openCoverAppComplex (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hI : Injective I) :
    (openCoverAppComplex A V₁ V₂ I).ShortExact :=
  have := hI
  ShortComplex.shortExact_of_iso (openCoverAppComplexIso A V₁ V₂ I).symm
    (openCoverShortComplex_shortExact A hV I)

/-- **The long exact sequence of the Mayer--Vietoris short complex of section functors** of an open
covering `X = X' ∪ X''`, at a fixed object `(U, T, δ)` of `Cris(X/S)`: the right derived functors
of sections over `(U, T, δ)`, of the sum of sections over the `X'`- and `X''`-parts, and of
sections over the `X'''`-part fit into a long exact sequence, natural in the abelian sheaf.

This is an object-level relative of [Stacks, Tag 07ML], not the remark, which is the
distinguished triangle of the derived direct images `Rf_{cris, *}` in `D(𝒪_{X'/S'})`,
`...SmallSite.exists_distinguished_triangle_derivedCrisModuleDirectImage`. -/
theorem longExact_openCoverFunctorComplex (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) :
    ∃ delta : ∀ n : ℕ, (openCoverFunctorComplex A V₁ V₂).X₃.rightDerived n ⟶
        (openCoverFunctorComplex A V₁ V₂).X₁.rightDerived (n + 1),
      (∀ F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1},
          Mono ((NatTrans.rightDerived (openCoverFunctorComplex A V₁ V₂).f 0).app F)) ∧
        ∀ (n : ℕ) (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}),
          (ComposableArrows.mk₅
            ((NatTrans.rightDerived (openCoverFunctorComplex A V₁ V₂).f n).app F)
            ((NatTrans.rightDerived (openCoverFunctorComplex A V₁ V₂).g n).app F)
            ((delta n).app F)
            ((NatTrans.rightDerived (openCoverFunctorComplex A V₁ V₂).f (n + 1)).app F)
            ((NatTrans.rightDerived (openCoverFunctorComplex A V₁ V₂).g (n + 1)).app F)).Exact :=
  longExact_rightDerived_of_shortExact_on_injectives (openCoverFunctorComplex A V₁ V₂).f
    (openCoverFunctorComplex A V₁ V₂).g (openCoverFunctorComplex A V₁ V₂).zero
    (shortExact_openCoverAppComplex A hV)

variable [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]

/-- **The Mayer--Vietoris triangle of an open covering `X = X' ∪ X''` at an object `(U, T, δ)` of
`Cris(X/S)` and a cochain complex `K` of injective abelian sheaves**: the triangle

`Γ((U, T, δ), K) ⟶ Γ(X'-part of (U, T, δ), K) ⊕ Γ(X''-part, K) ⟶ Γ(X'''-part, K) ⟶ [1]`

in the derived category of abelian groups.  That it is distinguished is
`openCoverTriangle_distinguished`. -/
def openCoverTriangle (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤)
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ n, Injective (K.X n)) : Triangle (DerivedCategory AddCommGrpCat.{u + 1}) :=
  triangleOfInjectiveCochainComplex (openCoverFunctorComplex A V₁ V₂).f
    (openCoverFunctorComplex A V₁ V₂).g (openCoverFunctorComplex A V₁ V₂).zero
    (shortExact_openCoverAppComplex A hV) K hK

/-- The first term of the Mayer--Vietoris triangle is the complex of sections of `K` over
`(U, T, δ)`. -/
theorem openCoverTriangle_obj₁ (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    (openCoverTriangle A hV K hK).obj₁ =
      DerivedCategory.Q.obj
        (((sectionsFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  rfl

/-- The middle term of the Mayer--Vietoris triangle is the direct sum of the complexes of
sections of `K` over the restrictions of `(U, T, δ)` to `X'` and to `X''`. -/
theorem openCoverTriangle_obj₂ (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    (openCoverTriangle A hV K hK).obj₂ =
      DerivedCategory.Q.obj
        ((((sectionsFunctor (openCoverSquare A V₁ V₂).X₂) ⊞
          (sectionsFunctor (openCoverSquare A V₁ V₂).X₃)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  rfl

/-- The third term of the Mayer--Vietoris triangle is the complex of sections of `K` over the
restriction of `(U, T, δ)` to `X''' = X' ∩ X''`. -/
theorem openCoverTriangle_obj₃ (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    (openCoverTriangle A hV K hK).obj₃ =
      DerivedCategory.Q.obj
        (((sectionsFunctor (openCoverSquare A V₁ V₂).X₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  rfl

/-- **The Mayer--Vietoris triangle of an open covering `X = X' ∪ X''` at a fixed object of the
small crystalline site is distinguished**: for every object `(U, T, δ)` of `Cris(X/S)` and every
cochain complex `K` of injective abelian sheaves on `Cris(X/S)`,

`Γ((U, T, δ), K) ⟶ Γ(X'-part, K) ⊕ Γ(X''-part, K) ⟶ Γ(X'''-part, K) ⟶ [1]`

is a distinguished triangle of `D(Ab)`.

This is an object-level relative of [Stacks, Tag 07ML], not the remark: the remark is the
distinguished triangle of the derived direct images `Rf_{cris, *}F`,
`Rf'_{cris, *}F' ⊕ Rf''_{cris, *}F''`, `Rf'''_{cris, *}F'''` in `D(𝒪_{X'/S'})`, which is
`...SmallSite.exists_distinguished_triangle_derivedCrisModuleDirectImage` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisDirectImage.lean`. -/
theorem openCoverTriangle_distinguished (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    openCoverTriangle A hV K hK ∈ distTriang (DerivedCategory AddCommGrpCat.{u + 1}) :=
  triangleOfInjectiveCochainComplex_distinguished (openCoverFunctorComplex A V₁ V₂).f
    (openCoverFunctorComplex A V₁ V₂).g (openCoverFunctorComplex A V₁ V₂).zero
    (shortExact_openCoverAppComplex A hV) K hK

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
