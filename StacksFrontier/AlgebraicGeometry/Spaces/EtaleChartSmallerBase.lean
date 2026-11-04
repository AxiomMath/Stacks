module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction

/-!
# The étale-chart condition and a change of base scheme (Stacks 03I5 (2), 03MJ, 04SG)

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2), which carries a
presheaf on the big fppf site of `W` to a presheaf on the big fppf site of `S`. A section of
`Λ_h F` over an object `V` of the site of `S` is a factorization `ψ : V.left ⟶ W` of the structure
morphism of `V` together with a section of `F` over `(V.left, ψ)`.

This file proves that the every-étale-chart condition of Stacks 03MJ is **unchanged** by `Λ_h`:
for every property `P` of morphisms of schemes and every `k : F ⟶ G` of presheaves on the big fppf
site of `W`, `P` holds on every étale chart of `Λ_h k` exactly when it holds on every étale chart
of `k`. Consequently the condition for the *structural* morphism
`CategoryTheory.OverShriek.relocalizeToYoneda h F : Λ_h F ⟶ h_{(W ⟶ S)}` does not depend on `S` at
all, so an algebraic space over `W`, viewed over `S` and then over a larger base `S'`, has the
same every-étale-chart conditions on both.

That is the step the presentation clause of Stacks 026O needs in order to be transferred along
Construction A of Stacks 04X5: smoothness of a morphism of algebraic spaces
(`AlgebraicGeometry.Space.IsSmooth`, Stacks 03ZC part (1)) is the every-étale-chart condition for
the smooth property of morphisms of schemes, and the morphism it is tested on is the structural
morphism of the image of Stacks 04SG's forward functor.

## Main results

* `AlgebraicGeometry.presheaf_relocalizeChart_iff`: a property of a chart tested on representable
  base changes — in particular being an étale chart — is unchanged by the lower-shriek extension.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`: the every-étale-chart
  condition of **Stacks 03MJ** is unchanged by the lower-shriek extension.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_comp_iff` and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`: the
  every-étale-chart condition for the structural morphism of an algebraic space over `W`, read
  over a base, does not depend on the base.

## Implementation notes

The argument has three parts, and none of them uses the fppf topology.

First, every chart of `Λ_h F` is the extension of a chart of `F`
(`AlgebraicGeometry.exists_relocalizeChart`): a morphism from a representable presheaf into
`Λ_h F` is a section, hence a factorization `ψ` together with a section of `F`, and the object it
is defined on is the image under `CategoryTheory.Over.map h` of `(V.left, ψ)` up to a canonical
isomorphism with identity underlying morphism (`AlgebraicGeometry.relocalizeBaseHom`). The chart
data over the two bases are therefore in bijection, with the same underlying schemes and the same
underlying morphisms of schemes, which is why `P` is tested on the same morphisms on both sides.

Second, being an étale chart is unchanged (`AlgebraicGeometry.presheaf_relocalizeChart_iff`),
because `Λ_h` preserves fibre products (the source's appeal to Sites 04BB, which is
`AlgebraicGeometry.relocalizePresheaf_preservesConnectedLimits`) and also *reflects* them
(`AlgebraicGeometry.relocalizePresheaf_reflectsPullbacks`), and it carries representable presheaves
to representable presheaves (Stacks 03I4 part (2), `AlgebraicGeometry.relocalizedYonedaIso`). So a
representable base change of a chart over one base is the extension of a representable base change
over the other, with the same underlying morphism of schemes.

Third, a commuting square of extended charts comes from a commuting square of charts. This is
where the extension's own structural morphism is used: composing an extended chart with
`CategoryTheory.OverShriek.relocalizeToYoneda` reads off the factorization through `W` and
forgets the chart (`AlgebraicGeometry.relocalizeChart_comp_relocalizeToYoneda`), so the square
forces the two factorizations to agree, after which the extension's faithfulness
(`AlgebraicGeometry.relocalizePresheaf_faithful`) gives the square over `W`.

The reduction of the structural morphism to a condition over `W` alone is that
`CategoryTheory.OverShriek.relocalizeToYoneda h F` is `Λ_h` of the structural morphism of `F` to
the representable presheaf of the identity of `W` — the terminal object of the big fppf site of
`W` — followed by an isomorphism (`AlgebraicGeometry.relocalizeToYoneda_eq_map_toYonedaId` and
`AlgebraicGeometry.isIso_relocalizeToYoneda_yonedaId`). The every-étale-chart condition is
invariant under composing with an isomorphism on either side
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iso_comp_iff` and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp_iso_iff`), which is also what carries the
statement over to the structural morphism that Stacks 04SG's forward functor produces, through
`AlgebraicGeometry.Space.relocalizeToYoneda_eq`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

attribute [local instance] etale_scheme_respectsIso

/-! ### Exactness and faithfulness of the lower-shriek extension -/

/-- `CategoryTheory.Over.map f` reflects isomorphisms: a morphism over `Y` is an isomorphism as
soon as its underlying morphism is, and that is unchanged by `CategoryTheory.Over.map f`. -/
theorem overMap_reflectsIsomorphisms {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    (Over.map f).ReflectsIsomorphisms where
  reflects {A B} m _ := by
    have _ : IsIso ((Over.forget X).map m) := by
      have := (Over.forget Y).map_isIso ((Over.map f).map m)
      exact this
    exact isIso_of_reflects_iso m (Over.forget X)

/-- `CategoryTheory.Over.map f` is faithful: it does not change the underlying morphism. -/
theorem overMap_faithful {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    (Over.map f).Faithful := by
  have _ : (Over.map f ⋙ Over.forget Y).Faithful := by
    rw [Over.mapForget_eq]
    infer_instance
  exact Functor.Faithful.of_comp (Over.map f) (Over.forget Y)

/-- The presheaf-level lower-shriek extension is faithful: under the equivalences of Stacks 00Y1
it is `CategoryTheory.Over.map (yoneda.map g)`, which is faithful. -/
theorem relocalizePresheaf_faithful {C : Type u} [Category.{v} C] {V U : C} (g : V ⟶ U) :
    (OverShriek.relocalizePresheafFunctor g).Faithful := by
  have _ := overMap_faithful (yoneda.map g)
  show ((OverShriek.presheafEquivalence (U := V)).functor ⋙
    Over.map (yoneda.map g) ⋙ (OverShriek.presheafEquivalence (U := U)).inverse).Faithful
  infer_instance

/-- The presheaf-level lower-shriek extension **reflects** fibre products. It preserves them
(`AlgebraicGeometry.relocalizePresheaf_preservesConnectedLimits`) and reflects isomorphisms, and
a presheaf category has all fibre products, so reflection follows. -/
theorem relocalizePresheaf_reflectsPullbacks {C : Type u} [Category.{v} C] {V U : C} (g : V ⟶ U) :
    ReflectsLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor g) := by
  have _ := overMap_reflectsIsomorphisms (yoneda.map g)
  have _ : PreservesLimitsOfShape WalkingCospan (Over.map (yoneda.map g)) := by
    have _ : PreservesLimitsOfShape WalkingCospan
        (Over.map (yoneda.map g) ⋙ Over.forget (yoneda.obj U)) := by
      rw [Over.mapForget_eq]
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (Over.map (yoneda.map g)) (Over.forget (yoneda.obj U))
  have _ : ReflectsLimitsOfShape WalkingCospan (Over.map (yoneda.map g)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  show ReflectsLimitsOfShape WalkingCospan
    ((OverShriek.presheafEquivalence (U := V)).functor ⋙
      Over.map (yoneda.map g) ⋙ (OverShriek.presheafEquivalence (U := U)).inverse)
  infer_instance

/-! ### Charts of a lower-shriek extension -/

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- A chart of the lower-shriek extension `Λ_h F` obtained from a chart of `F`: the extension of
`a : h_U ⟶ F`, read through the identification of `Λ_h h_U` with the representable presheaf of `U`
viewed over `S` (Stacks 03I4 part (2)). -/
noncomputable def relocalizeChart {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F) :
    yoneda.obj ((Over.map h).obj U) ⟶ (OverShriek.relocalizePresheafFunctor h).obj F :=
  (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U).inv ≫
    (OverShriek.relocalizePresheafFunctor h).map a

/-- The canonical morphism `U ⟶ (W ⟶ S)` of the big fppf site of `S` attached to an object `U` of
the big fppf site of `W`: it is `U.hom` on underlying schemes. -/
def relocalizeOverHom (U : BigFppfOver B W hW) : (Over.map h).obj U ⟶ Over.mk h :=
  Over.homMk U.hom rfl

/-- Every object `U'` of the big fppf site of `S` whose structure morphism factors through `W` is
the image under `CategoryTheory.Over.map h` of an object of the big fppf site of `W` with the same
underlying scheme, and the comparison is an isomorphism with identity underlying morphism. -/
def relocalizeBaseHom {U' : BigFppfOver B S hS} {ψ : U'.left ⟶ B.obj hW}
    (hψ : ψ ≫ h = U'.hom) : U' ⟶ (Over.map h).obj (Over.mk ψ) :=
  Over.homMk (𝟙 U'.left) (by simpa using hψ)

/-- `AlgebraicGeometry.relocalizeBaseHom` is an isomorphism, since its underlying morphism of
schemes is the identity. -/
instance isIso_relocalizeBaseHom {U' : BigFppfOver B S hS} {ψ : U'.left ⟶ B.obj hW}
    (hψ : ψ ≫ h = U'.hom) : IsIso (relocalizeBaseHom B W S hW hS h hψ) := by
  have _ : IsIso ((Over.forget (B.obj hS)).map (relocalizeBaseHom B W S hW hS h hψ)) := by
    change IsIso (𝟙 U'.left)
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))

/-- `AlgebraicGeometry.relocalizeBaseHom` is the identity on underlying schemes. -/
theorem relocalizeBaseHom_left {U' : BigFppfOver B S hS} {ψ : U'.left ⟶ B.obj hW}
    (hψ : ψ ≫ h = U'.hom) : (relocalizeBaseHom B W S hW hS h hψ).left = 𝟙 U'.left :=
  rfl

/-- The inverse of `AlgebraicGeometry.relocalizeBaseHom` is the identity on underlying
schemes. -/
theorem inv_relocalizeBaseHom_left {U' : BigFppfOver B S hS} {ψ : U'.left ⟶ B.obj hW}
    (hψ : ψ ≫ h = U'.hom) :
    (inv (relocalizeBaseHom B W S hW hS h hψ)).left = 𝟙 U'.left := by
  have hh := congrArg Over.Hom.left (IsIso.hom_inv_id (relocalizeBaseHom B W S hW hS h hψ))
  rw [Over.comp_left, relocalizeBaseHom_left] at hh
  simpa using hh

/-- **Every chart of a lower-shriek extension is the extension of a chart.** A morphism from the
representable presheaf of `U'` to `Λ_h F` is a section of `Λ_h F` over `U'`, that is a
factorization `ψ` of the structure morphism of `U'` through `W` together with a section of `F` over
`(U'.left, ψ)`; so it is `AlgebraicGeometry.relocalizeChart` of a chart of `F`, read through the
comparison `AlgebraicGeometry.relocalizeBaseHom`. -/
theorem exists_relocalizeChart {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (U' : BigFppfOver B S hS)
    (a' : yoneda.obj U' ⟶ (OverShriek.relocalizePresheafFunctor h).obj F) :
    ∃ (ψ : U'.left ⟶ B.obj hW) (hψ : ψ ≫ h = U'.hom) (a : yoneda.obj (Over.mk ψ) ⟶ F),
      a' = yoneda.map (relocalizeBaseHom B W S hW hS h hψ) ≫
        relocalizeChart B W S hW hS h a := by
  classical
  let x := yonedaEquiv a'
  have hx : yonedaEquiv a' = x := rfl
  rcases x with ⟨⟨ψ, s⟩, hψ⟩
  have hψ' : ψ ≫ h = U'.hom := hψ
  let U : BigFppfOver B W hW := Over.mk ψ
  let a : yoneda.obj U ⟶ F := yonedaEquiv.symm s
  refine ⟨ψ, hψ', a, ?_⟩
  apply yonedaEquiv.injective
  let ρ := relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U
  have hρ : ρ.inv.app (op U') (relocalizeBaseHom B W S hW hS h hψ')
      = ⟨⟨ψ, (𝟙 U : U ⟶ U)⟩, hψ⟩ := by
    show (relocalizedYonedaRepresentableBy B (B.obj hW) (B.obj hS) h U).homEquiv
      (relocalizeBaseHom B W S hW hS h hψ') = ⟨⟨ψ, (𝟙 U : U ⟶ U)⟩, hψ⟩
    apply Subtype.ext
    apply Sigma.ext
    · dsimp [relocalizedYonedaRepresentableBy]
      show Over.Hom.left (relocalizeBaseHom B W S hW hS h hψ') ≫ U.hom = ψ
      show 𝟙 U'.left ≫ ψ = ψ
      simp
    · dsimp [relocalizedYonedaRepresentableBy]
      apply heq_of_eq
      apply Over.OverMorphism.ext
      show 𝟙 U'.left = 𝟙 U'.left
      rfl
  rw [hx, yonedaEquiv_apply]
  have hEval : ((yoneda.map (relocalizeBaseHom B W S hW hS h hψ') ≫
        relocalizeChart B W S hW hS h a).app (op U')) (𝟙 U') =
      ((OverShriek.relocalizePresheafFunctor h).map a).app (op U')
        (ρ.inv.app (op U') (relocalizeBaseHom B W S hW hS h hψ')) := rfl
  rw [hEval, hρ]
  apply Subtype.ext
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    show s = a.app (op U) (𝟙 U)
    simp [a]

/-- The extension of a chart of `F`, followed by the structural morphism of `Λ_h F`, reads off the
structure morphism of the chart's object: it is the canonical morphism
`AlgebraicGeometry.relocalizeOverHom`, independently of the chart. -/
theorem relocalizeChart_comp_relocalizeToYoneda {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F) :
    relocalizeChart B W S hW hS h a ≫ OverShriek.relocalizeToYoneda h F =
      yoneda.map (relocalizeOverHom B W S hW hS h U) := by
  ext V k
  exact Over.OverMorphism.ext rfl

/-- The structural morphism of a lower-shriek extension is natural: it does not see the presheaf
it is the extension of. -/
theorem relocalizeToYoneda_naturality {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor h).map k ≫ OverShriek.relocalizeToYoneda h G =
      OverShriek.relocalizeToYoneda h F := by
  ext V x
  exact Over.OverMorphism.ext rfl

/-- Extending a chart is compatible with postcomposition. -/
theorem relocalizeChart_comp {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F) (k : F ⟶ G) :
    relocalizeChart B W S hW hS h a ≫ (OverShriek.relocalizePresheafFunctor h).map k =
      relocalizeChart B W S hW hS h (a ≫ k) := by
  simp [relocalizeChart, Functor.map_comp]

/-- Extending a chart is compatible with precomposition by a morphism of the site. -/
theorem relocalizeChart_naturality {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B W hW} (m : U ⟶ V) (b : yoneda.obj V ⟶ F) :
    yoneda.map ((Over.map h).map m) ≫ relocalizeChart B W S hW hS h b =
      relocalizeChart B W S hW hS h (yoneda.map m ≫ b) := by
  have hnat := relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h m
  simp only [relocalizeChart, Functor.map_comp, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, hnat]
  simp

/-! ### Representable base changes of a chart -/

/-- **The extension of a representable base change of a chart is a representable base change of
the extended chart.** The extension preserves fibre products
(`AlgebraicGeometry.relocalizePresheaf_preservesConnectedLimits`) and carries representable
presheaves to representable presheaves (Stacks 03I4 part (2)). -/
theorem isPullback_relocalizeChart {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U V T : BigFppfOver B W hW} {a : yoneda.obj U ⟶ F} {e : yoneda.obj V ⟶ F}
    {p : T ⟶ U} {r : T ⟶ V}
    (hp : IsPullback (yoneda.map p) (yoneda.map r) a e) :
    IsPullback (yoneda.map ((Over.map h).map p)) (yoneda.map ((Over.map h).map r))
      (relocalizeChart B W S hW hS h a) (relocalizeChart B W S hW hS h e) := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  refine (hp.map (OverShriek.relocalizePresheafFunctor h)).of_iso
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T)
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U)
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h V)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h p
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h r
  · simp [relocalizeChart]
  · simp [relocalizeChart]

/-- The converse of `AlgebraicGeometry.isPullback_relocalizeChart`: the extension **reflects**
fibre products (`AlgebraicGeometry.relocalizePresheaf_reflectsPullbacks`) and is faithful, so a
square of charts which becomes a fibre product after extension is already one. -/
theorem isPullback_of_isPullback_relocalizeChart
    {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {U V T : BigFppfOver B W hW} {a : yoneda.obj U ⟶ F} {e : yoneda.obj V ⟶ F}
    {p : T ⟶ U} {r : T ⟶ V}
    (hp : IsPullback (yoneda.map ((Over.map h).map p)) (yoneda.map ((Over.map h).map r))
      (relocalizeChart B W S hW hS h a) (relocalizeChart B W S hW hS h e)) :
    IsPullback (yoneda.map p) (yoneda.map r) a e := by
  have _ : ReflectsLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_reflectsPullbacks h
  have _ := relocalizePresheaf_faithful h
  have key : IsPullback ((OverShriek.relocalizePresheafFunctor h).map (yoneda.map p))
      ((OverShriek.relocalizePresheafFunctor h).map (yoneda.map r))
      ((OverShriek.relocalizePresheafFunctor h).map a)
      ((OverShriek.relocalizePresheafFunctor h).map e) := by
    refine hp.of_iso
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T).symm
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U).symm
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h V).symm
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc,
        ← relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h p]
      simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc,
        ← relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h r]
      simp
    · simp [relocalizeChart]
    · simp [relocalizeChart]
  exact IsPullback.of_map (OverShriek.relocalizePresheafFunctor h)
    ((OverShriek.relocalizePresheafFunctor h).map_injective (by simpa using key.w)) key

/-- **A property of a chart, tested on representable base changes, is unchanged by the
lower-shriek extension.** This is the presheaf-level form of the base-change argument of Stacks
03I4 part (3): every chart of the extension is the extension of a chart
(`AlgebraicGeometry.exists_relocalizeChart`), the representable base changes correspond
(`AlgebraicGeometry.isPullback_relocalizeChart` and its converse), and corresponding base changes
have the same underlying morphism of schemes. -/
theorem presheaf_relocalizeChart_iff (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
        (relocalizeChart B W S hW hS h a) ↔
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B W hW)).presheaf a := by
  have _ := relocalizePresheaf_faithful h
  constructor
  · intro ha'
    refine MorphismProperty.relative.of_exists (F := yoneda) ?_
    intro V₀ e₀
    have hsq := ha'.1.isPullback' (relocalizeChart B W S hW hS h e₀)
    have hQ' := ha'.2 _ _ _ hsq
    set T' := ha'.1.pullback (relocalizeChart B W S hW hS h e₀) with hT'def
    set snd' := ha'.1.snd (relocalizeChart B W S hW hS h e₀) with hsnd'def
    set φ' : T' ⟶ (Over.map h).obj U := ha'.1.fst' (relocalizeChart B W S hW hS h e₀) with hφ'def
    have hbase : φ' ≫ relocalizeOverHom B W S hW hS h U
        = snd' ≫ relocalizeOverHom B W S hW hS h V₀ := by
      apply yoneda.map_injective
      rw [yoneda.map_comp, yoneda.map_comp,
        ← relocalizeChart_comp_relocalizeToYoneda B W S hW hS h a,
        ← relocalizeChart_comp_relocalizeToYoneda B W S hW hS h e₀,
        ← Category.assoc, ← Category.assoc, hsq.w]
    have hleft : φ'.left ≫ U.hom = snd'.left ≫ V₀.hom := congrArg Over.Hom.left hbase
    have hτ : (snd'.left ≫ V₀.hom) ≫ h = T'.hom := by
      rw [Category.assoc]
      exact Over.w snd'
    set T₀ : BigFppfOver B W hW := Over.mk (snd'.left ≫ V₀.hom) with hT₀def
    set r₀ : T₀ ⟶ V₀ := Over.homMk snd'.left rfl with hr₀def
    set p₀ : T₀ ⟶ U := Over.homMk φ'.left hleft with hp₀def
    set ιT := relocalizeBaseHom B W S hW hS h hτ with hιTdef
    have h1 : ιT ≫ (Over.map h).map p₀ = φ' := by
      apply Over.OverMorphism.ext
      show 𝟙 T'.left ≫ φ'.left = φ'.left
      simp
    have h2 : ιT ≫ (Over.map h).map r₀ = snd' := by
      apply Over.OverMorphism.ext
      show 𝟙 T'.left ≫ snd'.left = snd'.left
      simp
    have hpullS : IsPullback (yoneda.map ((Over.map h).map p₀))
        (yoneda.map ((Over.map h).map r₀))
        (relocalizeChart B W S hW hS h a) (relocalizeChart B W S hW hS h e₀) := by
      refine hsq.of_iso (yoneda.mapIso (asIso ιT)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ?_ ?_ ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, asIso_hom]
        rw [← yoneda.map_comp, h1]
      · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, asIso_hom]
        rw [← yoneda.map_comp, h2]
      · simp
      · simp
    exact ⟨T₀, yoneda.map p₀, r₀,
      isPullback_of_isPullback_relocalizeChart B W S hW hS h hpullS, hQ'⟩
  · intro ha
    refine MorphismProperty.relative.of_exists (F := yoneda) ?_
    intro V' e'
    obtain ⟨ψ, hψ, e₀, he⟩ := exists_relocalizeChart B W S hW hS h V' e'
    have hpullW := ha.1.isPullback' e₀
    have hQr₀ := ha.2 _ _ _ hpullW
    set T₀ := ha.1.pullback e₀ with hT₀def
    set r₀ := ha.1.snd e₀ with hr₀def
    set p₀ : T₀ ⟶ U := ha.1.fst' e₀ with hp₀def
    have hpullS := isPullback_relocalizeChart B W S hW hS h hpullW
    set ι := relocalizeBaseHom B W S hW hS h hψ with hιdef
    refine ⟨(Over.map h).obj T₀, yoneda.map ((Over.map h).map p₀),
      (Over.map h).map r₀ ≫ inv ι, ?_, ?_⟩
    · refine hpullS.of_iso (Iso.refl _) (Iso.refl _)
        (yoneda.mapIso (asIso ι)).symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp [he]
    · have hbase : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS))
          ((Over.map h).map r₀) := hQr₀
      exact MorphismProperty.RespectsIso.postcomp Q
        ((BigFppfOver.toScheme B S hS).map (inv ι))
        ((BigFppfOver.toScheme B S hS).map ((Over.map h).map r₀)) hbase

/-! ### The étale-chart condition -/

/-- The every-étale-chart condition of Stacks 03MJ is unchanged by precomposition with an
isomorphism of presheaves: the chart of the source is composed with the comparison. -/
theorem Space.holdsOnEveryEtaleChart_iso_comp_iff (P : MorphismProperty Scheme.{u})
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ F') [IsIso e] (f : F' ⟶ G) :
    Space.HoldsOnEveryEtaleChart B S hS P (e ≫ f) ↔
      Space.HoldsOnEveryEtaleChart B S hS P f := by
  constructor
  · intro hef U V a b m ha hb hsq
    refine hef U V (a ≫ inv e) b m
      ((MorphismProperty.cancel_right_of_respectsIso _ a (inv e)).2 ha) hb ?_
    rw [Category.assoc, ← Category.assoc (inv e), IsIso.inv_hom_id, Category.id_comp]
    exact hsq
  · intro hf U V a b m ha hb hsq
    refine hf U V (a ≫ e) b m
      ((MorphismProperty.cancel_right_of_respectsIso _ a e).2 ha) hb ?_
    rw [Category.assoc]
    exact hsq

/-- The every-étale-chart condition of Stacks 03MJ is unchanged by postcomposition with an
isomorphism of presheaves: the chart of the target is composed with the comparison. -/
theorem Space.holdsOnEveryEtaleChart_comp_iso_iff (P : MorphismProperty Scheme.{u})
    {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (θ : G ⟶ G') [IsIso θ] :
    Space.HoldsOnEveryEtaleChart B S hS P (f ≫ θ) ↔
      Space.HoldsOnEveryEtaleChart B S hS P f := by
  constructor
  · intro hfθ U V a b m ha hb hsq
    refine hfθ U V a (b ≫ θ) m ha
      ((MorphismProperty.cancel_right_of_respectsIso _ b θ).2 hb) ?_
    rw [← Category.assoc, hsq, Category.assoc]
  · intro hf U V a b m ha hb hsq
    refine hf U V a (b ≫ inv θ) m ha
      ((MorphismProperty.cancel_right_of_respectsIso _ b (inv θ)).2 hb) ?_
    rw [← Category.assoc, hsq]
    simp

/-- **The every-étale-chart condition of Stacks 03MJ is unchanged by the lower-shriek extension of
Stacks 03I5 part (2).**

Every chart of the extension is the extension of a chart
(`AlgebraicGeometry.exists_relocalizeChart`), being étale is unchanged
(`AlgebraicGeometry.presheaf_relocalizeChart_iff`), a commuting square of extended charts comes
from a commuting square of charts because the factorization through `W` that a section of the
extension carries is determined, and corresponding charts have the same underlying morphism of
schemes. -/
theorem Space.holdsOnEveryEtaleChart_relocalizeMap_iff (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :
    Space.HoldsOnEveryEtaleChart B S hS P ((OverShriek.relocalizePresheafFunctor h).map k) ↔
      Space.HoldsOnEveryEtaleChart B W hW P k := by
  have _ := relocalizePresheaf_faithful h
  constructor
  · intro hbig U₀ V₀ a b m ha hb hsq
    refine hbig ((Over.map h).obj U₀) ((Over.map h).obj V₀)
      (relocalizeChart B W S hW hS h a) (relocalizeChart B W S hW hS h b)
      ((Over.map h).map m)
      ((presheaf_relocalizeChart_iff B W S hW hS h _ a).2 ha)
      ((presheaf_relocalizeChart_iff B W S hW hS h _ b).2 hb) ?_
    rw [relocalizeChart_naturality, relocalizeChart_comp, hsq]
  · intro hsmall U' V' a' b' m' ha' hb' hsq'
    obtain ⟨ψU, hψU, a, hae⟩ := exists_relocalizeChart B W S hW hS h U' a'
    obtain ⟨ψV, hψV, b, hbe⟩ := exists_relocalizeChart B W S hW hS h V' b'
    set ιU := relocalizeBaseHom B W S hW hS h hψU with hιU
    set ιV := relocalizeBaseHom B W S hW hS h hψV with hιV
    set n : (Over.map h).obj (Over.mk ψU) ⟶ (Over.map h).obj (Over.mk ψV) :=
      inv ιU ≫ m' ≫ ιV with hndef
    have hnleft : n.left = m'.left := by
      rw [hndef, Over.comp_left, Over.comp_left, inv_relocalizeBaseHom_left,
        relocalizeBaseHom_left]
      simp
    have hnsq : yoneda.map n ≫ relocalizeChart B W S hW hS h b =
        relocalizeChart B W S hW hS h a ≫ (OverShriek.relocalizePresheafFunctor h).map k := by
      rw [hndef, yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        show yoneda.map ιV ≫ relocalizeChart B W S hW hS h b = b' from hbe.symm, hsq', hae,
        Category.assoc, ← Category.assoc (yoneda.map (inv ιU)), ← yoneda.map_comp,
        IsIso.inv_hom_id, yoneda.map_id, Category.id_comp]
    have hfac : n ≫ relocalizeOverHom B W S hW hS h (Over.mk ψV)
        = relocalizeOverHom B W S hW hS h (Over.mk ψU) := by
      apply yoneda.map_injective
      rw [yoneda.map_comp, ← relocalizeChart_comp_relocalizeToYoneda B W S hW hS h b,
        ← Category.assoc, hnsq, Category.assoc, relocalizeToYoneda_naturality,
        relocalizeChart_comp_relocalizeToYoneda]
    have hfacleft : n.left ≫ ψV = ψU := congrArg Over.Hom.left hfac
    set m₀ : (Over.mk ψU : BigFppfOver B W hW) ⟶ Over.mk ψV :=
      Over.homMk n.left hfacleft with hm₀def
    have hmap : (Over.map h).map m₀ = n := Over.OverMorphism.ext rfl
    have hsq₀ : yoneda.map m₀ ≫ b = a ≫ k := by
      apply (OverShriek.relocalizePresheafFunctor h).map_injective
      rw [Functor.map_comp, Functor.map_comp]
      have h1 : relocalizeChart B W S hW hS h (yoneda.map m₀ ≫ b) =
          relocalizeChart B W S hW hS h (a ≫ k) := by
        rw [← relocalizeChart_naturality, ← relocalizeChart_comp, hmap, hnsq]
      simp only [relocalizeChart, Functor.map_comp] at h1
      exact (Iso.cancel_iso_inv_left _ _ _).1 h1
    have hconc := hsmall (Over.mk ψU) (Over.mk ψV) a b m₀
      ((presheaf_relocalizeChart_iff B W S hW hS h _ a).1
        (by rw [hae] at ha'
            exact ((MorphismProperty.cancel_left_of_respectsIso _
              (yoneda.map ιU) _).1 ha')))
      ((presheaf_relocalizeChart_iff B W S hW hS h _ b).1
        (by rw [hbe] at hb'
            exact ((MorphismProperty.cancel_left_of_respectsIso _
              (yoneda.map ιV) _).1 hb')))
      hsq₀
    have hfin : (BigFppfOver.toScheme B W hW).map m₀
        = (BigFppfOver.toScheme B S hS).map m' := congrArg B.inclusion.map hnleft
    rw [hfin] at hconc
    exact hconc

/-! ### The structural morphism of a lower-shriek extension -/

/-- The structural morphism of a presheaf `F` on the big fppf site of `W` to the terminal
representable presheaf `h_{(W ⟶ W)}`. -/
def Space.toYonedaId (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hW))) where
  app Z := ↾fun _ => Over.homMk (unop Z).hom (by simp)
  naturality Z Z' f := by
    ext x
    refine Over.OverMorphism.ext ?_
    change (unop Z').hom = Over.Hom.left f.unop ≫ (unop Z).hom
    exact (Over.w f.unop).symm

/-- The inverse of the structural morphism of `Λ_h` of the terminal representable presheaf
`h_{(W ⟶ W)}` (see `AlgebraicGeometry.isIso_relocalizeToYoneda_yonedaId`). -/
def relocalizeIdInv : yoneda.obj (Over.mk h) ⟶
    (OverShriek.relocalizePresheafFunctor h).obj (yoneda.obj (Over.mk (𝟙 (B.obj hW)))) where
  app V := ↾fun k => OverShriek.relocalizeMk h (yoneda.obj (Over.mk (𝟙 (B.obj hW))))
    k.left (Over.homMk k.left (by simp)) (by simpa using Over.w k)
  naturality V V' f := by
    ext k
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Over.OverMorphism.ext
      rfl

/-- The structural morphism of `Λ_h` of the terminal representable presheaf `h_{(W ⟶ W)}` is an
isomorphism, with inverse `AlgebraicGeometry.relocalizeIdInv`. -/
instance isIso_relocalizeToYoneda_yonedaId :
    IsIso (OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hW))))) := by
  refine ⟨relocalizeIdInv B W S hW hS h, ?_, ?_⟩
  · ext V x
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Over.OverMorphism.ext
      change x.1.1 = Over.Hom.left x.1.2
      simpa using (Over.w x.1.2).symm
  · ext V k
    exact Over.OverMorphism.ext rfl

/-- The structural morphism of `Λ_h F` is `Λ_h` of the structural morphism
`AlgebraicGeometry.Space.toYonedaId` of `F`, followed by the structural morphism of `Λ_h` of the
terminal representable presheaf. -/
theorem relocalizeToYoneda_eq_map_toYonedaId (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizePresheafFunctor h).map (Space.toYonedaId B W hW F) ≫
        OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hW)))) =
      OverShriek.relocalizeToYoneda h F :=
  relocalizeToYoneda_naturality B W S hW hS h _


/-- **The every-étale-chart condition for the structural morphism of a lower-shriek extension does
not depend on the base.** It is the every-étale-chart condition, over `W` itself, for the
structural morphism of `F` to the terminal object of the big fppf site of `W`. -/
theorem Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff (P : MorphismProperty Scheme.{u})
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    Space.HoldsOnEveryEtaleChart B S hS P (OverShriek.relocalizeToYoneda h F) ↔
      Space.HoldsOnEveryEtaleChart B W hW P (Space.toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F]
  exact (Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS P _ _).trans
    (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h P _)

/-! ### Change of base scheme -/

section ChangeOfBase

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **The every-étale-chart condition of Stacks 03MJ for the structural morphism of an algebraic
space over `W` does not change when the base is enlarged.** Both sides are the condition over `W`
itself, by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`. -/
theorem Space.holdsOnEveryEtaleChart_relocalizeToYoneda_comp_iff (P : MorphismProperty Scheme.{u})
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    Space.HoldsOnEveryEtaleChart B S' hS' P (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      Space.HoldsOnEveryEtaleChart B S hS P (OverShriek.relocalizeToYoneda h F) :=
  (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) P F).trans
    (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S hW hS h P F).symm

end ChangeOfBase

section Forward

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **The every-étale-chart condition of Stacks 03MJ for the structural morphism of the image of
Stacks 04SG's forward functor does not depend on the base.** An algebraic space over `W`, viewed
over `S` along `h` and over `S'` along a factorization `h ≫ g`, has the same every-étale-chart
conditions on its structural morphism.

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_comp_iff`, read through
the identification `AlgebraicGeometry.Space.relocalizeToYoneda_eq` of that structural morphism with
the relocalization's own. The morphism to `S'` is taken as data, together with the factorization,
so that the statement applies to a given object of the big fppf site of `S'` without rewriting
inside the type of the morphism being tested. -/
theorem Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u) (P : MorphismProperty Scheme.{u})
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    Space.HoldsOnEveryEtaleChart B S' hS' P
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      Space.HoldsOnEveryEtaleChart B S hS P
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  have h1 := Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩
  have h2 := Space.relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩
  rw [← Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P
      ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _,
    ← Space.holdsOnEveryEtaleChart_iso_comp_iff B S' hS' P
      ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _,
    h1, h2]
  exact Space.holdsOnEveryEtaleChart_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g P F

end Forward

end AlgebraicGeometry

end
