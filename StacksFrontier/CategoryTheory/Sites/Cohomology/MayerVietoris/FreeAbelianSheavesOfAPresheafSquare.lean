module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Square
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology

/-!
# Free abelian sheaves on a square of presheaves of sets

Let `(C, J)` be a site and let

```
D ⟶ F
↓    ↓
E ⟶ G
```

be a commutative square of presheaves of sets on `C` whose sheafification is a pushout square
of sheaves of sets and whose map `D^# ⟶ F^#` is a monomorphism. These are the two hypotheses
of [Stacks, Tag 0EVZ]. This file extracts from them the short exact sequence of abelian sheaves

`0 ⟶ **Z**_D^# ⟶ **Z**_E^# ⊞ **Z**_F^# ⟶ **Z**_G^# ⟶ 0`

and the short exact sequence of sections of an injective abelian sheaf over the four presheaves
that it produces. The latter is the sheaf-theoretic content of Tag 0EVZ, and is to the square of
presheaves what
`Stacks.Cohomology.MayerVietoris.shortExact_sectionsShortComplex` is to a square of objects of
the site in [Stacks, Tag 0EVY].

## Main definitions

* `Stacks.MayerVietoris.PresheafSquare.freeAbelianSheafShortComplex`: the short complex
  `**Z**_D^# ⟶ **Z**_E^# ⊞ **Z**_F^# ⟶ **Z**_G^#` of abelian sheaves.
* `Stacks.MayerVietoris.PresheafSquare.presheafSections`: sections over a presheaf of sets,
  contravariantly in the presheaf, as a functor of the abelian sheaf. Sections over `K` are the
  morphisms out of the free abelian sheaf `**Z**_K^#`, which by the free/forget and
  sheafification adjunctions are the maps of presheaves of sets `K ⟶ ℱ`; that is the group
  `ℱ(K)` of [Stacks, Tag 079X].
* `Stacks.MayerVietoris.PresheafSquare.sectionsShortComplex`: the short complex
  `ℱ(G) ⟶ ℱ(E) ⊞ ℱ(F) ⟶ ℱ(D)` of sections, with the minus sign on the restriction from `F`.

## Main results

* `Stacks.MayerVietoris.PresheafSquare.isPushout_map_freeAbelianSheaf` and
  `Stacks.MayerVietoris.PresheafSquare.mono_freeAbelianSheaf_map`: the two hypotheses, carried
  from sheaves of sets to abelian sheaves.
* `Stacks.MayerVietoris.PresheafSquare.shortExact_freeAbelianSheafShortComplex`: the short exact
  sequence of free abelian sheaves.
* `Stacks.MayerVietoris.PresheafSquare.presheafSectionsEquiv`: sections over a presheaf of sets
  are the maps of presheaves of sets out of it.
* `Stacks.MayerVietoris.PresheafSquare.shortExact_sectionsShortComplex`: the sections short
  complex is short exact for every injective abelian sheaf.

## Implementation notes

The free abelian sheaf functor is defined on *presheaves* of sets, whereas the two hypotheses
are about the sheafifications. The passage between them is
`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso`, which identifies the free abelian
sheaf functor with sheafification followed by `CategoryTheory.Sheaf.composeAndSheafify`; the
latter is a left adjoint, hence preserves the pushout, and preserves monomorphisms because the
free abelian group functor does and sheafification is exact.

`CategoryTheory.Square` numbers `D, F, E, G` as `X₁, X₂, X₃, X₄`, and the minus sign sits on the
map out of `X₂`, matching the convention of
`Stacks.MayerVietoris.CanonicalMapOfComplexes`. Mathlib's `CategoryTheory.Square.cokernelCofork`
puts the minus sign on the map out of `X₃` instead, so the pushout is fed to it through
`CategoryTheory.Square.flip`.

Short-exactness of the sections is read off the pushout square itself rather than from the
short exact sequence of free abelian sheaves. The contravariant hom functor
`preadditiveYoneda.obj ℱ` preserves finite limits for every `ℱ`, so it carries the pushout
square, viewed in the opposite category, to a pullback square of abelian groups; the kernel
fork attached to that pullback by `CategoryTheory.Square.IsPullback.isLimitKernelFork` is
exactly the sections short complex, which gives both the monomorphism and the exactness in the
middle. Only the epimorphism uses injectivity of `ℱ`: there `preadditiveYoneda.obj ℱ`
preserves finite colimits as well, so it carries the epimorphism opposite to
`**Z**_D^# ⟶ **Z**_F^#` to an epimorphism, which is the second component of the last map.

For that reason sections are spelled `preadditiveYoneda.flip` rather than
`preadditiveCoyoneda`: the two are the same group of morphisms out of the free abelian sheaf,
but the limit and colimit preservation above is stated for `preadditiveYoneda.obj ℱ`, and the
flipped spelling makes the sections short complex that kernel fork on the nose.

## References

* [Stacks Project, Tag 0EVZ](https://stacks.math.columbia.edu/tag/0EVZ)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 079X](https://stacks.math.columbia.edu/tag/079X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.MayerVietoris.PresheafSquare

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{w}]

/-- **The sheafified pushout hypothesis, carried to abelian sheaves.** The free abelian sheaf
functor is sheafification followed by the free abelian sheaf functor on sheaves of sets, and
the latter is a left adjoint. -/
lemma isPushout_map_freeAbelianSheaf (sq : Square (Cᵒᵖ ⥤ Type w))
    (h : (sq.map (presheafToSheaf J (Type w))).IsPushout) :
    (sq.map (Presheaf.freeAbelianSheaf.{w} J)).IsPushout := by
  have : PreservesColimitsOfSize.{0, 0} (Sheaf.composeAndSheafify J AddCommGrpCat.free.{w}) :=
    (Sheaf.adjunction J AddCommGrpCat.adj.{w}).leftAdjoint_preservesColimits
  have h₂ : (sq.map (presheafToSheaf J (Type w) ⋙
      Sheaf.composeAndSheafify J AddCommGrpCat.free.{w})).IsPushout :=
    h.map (Sheaf.composeAndSheafify J AddCommGrpCat.free.{w})
  exact h₂.of_iso ((Square.mapFunctor.mapIso
    (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free.{w})).app sq)

/-- **The monomorphism hypothesis, carried to abelian sheaves.** The free abelian sheaf functor
on sheaves of sets preserves monomorphisms, being the underlying presheaf of sets followed by
the free abelian group functor and sheafification. -/
lemma mono_freeAbelianSheaf_map {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (hf : Mono ((presheafToSheaf J (Type w)).map f)) :
    Mono ((Presheaf.freeAbelianSheaf.{w} J).map f) := by
  have := hf
  have : Mono ((presheafToSheaf J (Type w) ⋙
      Sheaf.composeAndSheafify J AddCommGrpCat.free.{w}).map f) :=
    inferInstanceAs (Mono ((Sheaf.composeAndSheafify J AddCommGrpCat.free.{w}).map
      ((presheafToSheaf J (Type w)).map f)))
  have hAB : Mono ((presheafToSheaf J (Type w) ⋙
      Sheaf.composeAndSheafify J AddCommGrpCat.free.{w}).map f ≫
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free.{w}).hom.app Q) :=
    mono_comp _ _
  rw [(presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free.{w}).hom.naturality f] at hAB
  have := hAB
  have h₃ := mono_comp (inv ((presheafToSheafCompComposeAndSheafifyIso J
      AddCommGrpCat.free.{w}).hom.app P))
    ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free.{w}).hom.app P ≫
      ((Functor.whiskeringRight Cᵒᵖ (Type w) AddCommGrpCat.{w}).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{w}).map f)
  have h₄ : Mono (((Functor.whiskeringRight Cᵒᵖ (Type w) AddCommGrpCat.{w}).obj
      AddCommGrpCat.free ⋙ presheafToSheaf J AddCommGrpCat.{w}).map f) := by
    simpa only [IsIso.inv_hom_id_assoc] using h₃
  exact h₄

/-- The short complex `**Z**_D^# ⟶ **Z**_E^# ⊞ **Z**_F^# ⟶ **Z**_G^#` of abelian sheaves
attached to a square of presheaves of sets, with the minus sign on the map out of `X₂`. -/
def freeAbelianSheafShortComplex (sq : Square (Cᵒᵖ ⥤ Type w)) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk
    (biprod.lift ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₃)
      (-((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂)))
    (biprod.desc ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₃₄)
      ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₂₄))
    (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        ← sq.fac, add_neg_cancel])

/-- **The short exact sequence of free abelian sheaves of a Mayer-Vietoris square of presheaves
of sets.** The first map is a monomorphism because its second component is, and the remaining
two conditions say that the last map is a cokernel of the first, which is the pushout
hypothesis read through `CategoryTheory.Square.isPushoutEquivIsColimitCokernelCofork`. -/
theorem shortExact_freeAbelianSheafShortComplex (sq : Square (Cᵒᵖ ⥤ Type w))
    (hpushout : (sq.map (presheafToSheaf J (Type w))).IsPushout)
    (hmono : Mono ((presheafToSheaf J (Type w)).map sq.f₁₂)) :
    (freeAbelianSheafShortComplex J sq).ShortExact := by
  have hb : Mono ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂) :=
    mono_freeAbelianSheaf_map J sq.f₁₂ hmono
  have hcok : IsColimit ((sq.map (Presheaf.freeAbelianSheaf.{w} J)).flip).cokernelCofork :=
    ((isPushout_map_freeAbelianSheaf J sq hpushout).flip).isColimitCokernelCofork
  have hmf : Mono (freeAbelianSheafShortComplex J sq).f := by
    have h : Mono ((freeAbelianSheafShortComplex J sq).f ≫ biprod.snd) := by
      have he : (freeAbelianSheafShortComplex J sq).f ≫ biprod.snd =
          -((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂) := biprod.lift_snd _ _
      rw [he]
      exact (inferInstance : Mono (-((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂)))
    exact mono_of_mono _ biprod.snd
  have hexact : (freeAbelianSheafShortComplex J sq).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ hcok
  exact { exact := hexact
          mono_f := hmf
          epi_g := ((freeAbelianSheafShortComplex J sq).exact_and_epi_g_iff_g_is_cokernel.2
            ⟨hcok⟩).2 }

/-- **Sections over a presheaf of sets**, contravariantly in the presheaf and covariantly in
the abelian sheaf: the morphisms out of the free abelian sheaf on the presheaf. By the
free/forget and sheafification adjunctions these are the maps of presheaves of sets from the
presheaf to the underlying presheaf of the sheaf, which is the group `ℱ(K)` whose right derived
functors are the cohomology over `K` of [Stacks, Tag 079X]. -/
def presheafSections :
    (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤ (Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w}) :=
  (Presheaf.freeAbelianSheaf.{w} J).op ⋙ preadditiveYoneda.flip

/-- Sections over a fixed presheaf of sets are an additive functor of the abelian sheaf. -/
instance additive_presheafSections_obj (P : (Cᵒᵖ ⥤ Type w)ᵒᵖ) :
    ((presheafSections J).obj P).Additive where
  map_add := by intros; rfl

/-- **Sections over a presheaf of sets are the maps of presheaves of sets out of it**, which is
the group `ℱ(K) = Mor_{PSh(C)}(K, ℱ)` of [Stacks, Tag 079X]. This is the free/forget and
sheafification adjunction of
`CategoryTheory.Presheaf.freeAbelianSheafAdj`, and is what makes `presheafSections` the sections
functor rather than merely a corepresentable functor. -/
def presheafSectionsEquiv (P : Cᵒᵖ ⥤ Type w) (ℱ : Sheaf J AddCommGrpCat.{w}) :
    (((presheafSections J).obj (op P)).obj ℱ : Type max u w) ≃
      (P ⟶ (sheafToPresheaf J AddCommGrpCat.{w} ⋙ Presheaf.forgetAbelian).obj ℱ) :=
  (Presheaf.freeAbelianSheafAdj.{w} J).homEquiv P ℱ

/-- The short complex `ℱ(G) ⟶ ℱ(E) ⊞ ℱ(F) ⟶ ℱ(D)` of sections over the four presheaves of a
square, with the minus sign on the restriction from `F`. -/
def sectionsShortComplex (sq : Square (Cᵒᵖ ⥤ Type w)) (ℱ : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex AddCommGrpCat.{max u w} :=
  ShortComplex.mk
    (biprod.lift (((presheafSections J).map sq.f₃₄.op).app ℱ)
      (((presheafSections J).map sq.f₂₄.op).app ℱ))
    (biprod.desc (((presheafSections J).map sq.f₁₃.op).app ℱ)
      (-(((presheafSections J).map sq.f₁₂.op).app ℱ)))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, sq.fac, add_neg_cancel])

section Sections

variable (sq : Square (Cᵒᵖ ⥤ Type w))
  (hpushout : (sq.map (presheafToSheaf J (Type w))).IsPushout)
  (hmono : Mono ((presheafToSheaf J (Type w)).map sq.f₁₂))

include hpushout hmono

/-- **The sections short complex of a Mayer-Vietoris square of presheaves of sets is short exact
at an injective abelian sheaf.** This is the sheaf-theoretic content of [Stacks, Tag 0EVZ], and
generalises `Stacks.Cohomology.MayerVietoris.shortExact_sectionsShortComplex` from a square of
objects of the site to a square of presheaves of sets. -/
theorem shortExact_sectionsShortComplex (ℱ : Sheaf J AddCommGrpCat.{w}) (hℱ : Injective ℱ) :
    (sectionsShortComplex J sq ℱ).ShortExact := by
  have := hℱ
  have : PreservesFiniteColimits (preadditiveYoneda.obj ℱ) := by
    have h : preadditiveYoneda.obj ℱ = preadditiveYonedaObj ℱ ⋙ forget₂ _ AddCommGrpCat := rfl
    rw [h]
    exact comp_preservesFiniteColimits _ _
  have hb : Mono ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂) :=
    mono_freeAbelianSheaf_map J sq.f₁₂ hmono
  have hpull : (((sq.map (Presheaf.freeAbelianSheaf.{w} J)).op).map
      (preadditiveYoneda.obj ℱ)).IsPullback :=
    ((isPushout_map_freeAbelianSheaf J sq hpushout).op).map (preadditiveYoneda.obj ℱ)
  have hker := hpull.flip.isLimitKernelFork
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ShortComplex.exact_of_f_is_kernel _ hker
  · exact mono_of_isLimit_fork hker
  · have hg : biprod.inr ≫ (sectionsShortComplex J sq ℱ).g =
        -((preadditiveYoneda.obj ℱ).map
          ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂).op) := biprod.inr_desc _ _
    have h2 : Epi (biprod.inr ≫ (sectionsShortComplex J sq ℱ).g) := by
      rw [hg]
      exact (inferInstance : Epi (-((preadditiveYoneda.obj ℱ).map
        ((Presheaf.freeAbelianSheaf.{w} J).map sq.f₁₂).op)))
    exact epi_of_epi biprod.inr _

end Sections

end Stacks.MayerVietoris.PresheafSquare

end
