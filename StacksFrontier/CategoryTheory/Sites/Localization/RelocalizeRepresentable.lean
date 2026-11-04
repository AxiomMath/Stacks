module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Relocalization of a representable presheaf, and connected limits

Let `C` be a category and let `f : V ⟶ U` be a morphism of `C`.  Stacks 03EH attaches to `f` the
relocalization functor `j = Over.map f : C/V ⥤ C/U`, and its presheaf level lower shriek is
`CategoryTheory.OverShriek.relocalizePresheafFunctor f`, written `Λ` here:

```
  Λ G = (W --a--> U) ↦ { (ψ, s) | ψ : W ⟶ V, s ∈ G(W --ψ--> V), ψ ≫ f = a } .
```

Two structural facts about `Λ` are proved, the analogues for relocalization — and at the presheaf
level — of Stacks 03HU and Stacks 04BB for the localization lower shriek `j_{U!}`.

1. **`Λ` carries representables to representables**: `Λ h_Z ≅ h_{j Z}`, naturally in `Z`.  A
   section of `Λ h_Z` over `(W --a--> U)` is a factorization `a = ψ ≫ f` together with a morphism
   `(W --ψ--> V) ⟶ Z` of `C/V`; the morphism determines the factorization, so the data is exactly a
   morphism `(W --a--> U) ⟶ (Z.left --Z.hom ≫ f--> U)` of `C/U`.  This is
   `relocalizeYonedaIso`, and it is the presheaf level, general site form of Stacks 03I4 (2).
2. **`Λ` commutes with connected limits**, in particular with fibre products.  As in the source's
   proof of Stacks 04BB, this is read off from the identification of `Λ` with an operation on
   slices: `Λ` is by construction the presheaf level form of Stacks 00Y1,
   `Φ_V = presheafFunctorToOver : PSh(C/V) ≌ PSh(C)/h_V`, followed by `Over.map h_f` and by the
   inverse `Φ_U^{-1} = fiberFunctor 𝟙` of the same equivalence at `U`.  The two equivalences
   preserve all limits, and `Over.map` preserves the connected ones because
   `Over.map h ⋙ Over.forget = Over.forget` and `Over.forget` both preserves and reflects them.
   Connectedness is what the statement needs: `Λ` does *not* preserve the terminal presheaf, which
   it carries to `h_{j(⊤)} = h_{(V --f--> U)}` (`relocalizeTerminalIso`).

The two together say that `Λ` carries a fibre product over a representable presheaf to a fibre
product over a representable presheaf (`isPullback_map_relocalize`), and that every morphism from a
representable presheaf into `Λ G` is `Λ` of a morphism from a representable presheaf
(`exists_eq_relocalizeYonedaFactorIso_comp`).  Together they identify the represented base changes
of `Λ p` with `Λ` of the represented base changes of `p`, over objects of `C/V` with the same
underlying object of `C` (`isPullback_map_relocalize_of_factor`), and hence transport the morphism
property `P.presheaf` of Mathlib's `CategoryTheory.MorphismProperty.relative` across `Λ` in both
directions (`presheaf_map_relocalize` and `presheaf_of_presheaf_map_relocalize`).  That is the form
in which a property of a morphism of algebraic spaces over `S`, tested on scheme base changes, is
compared with the same property of the morphism viewed over a larger base.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeYonedaHom` and
  `CategoryTheory.OverShriek.relocalizeYonedaIso`: the comparison `Λ h_Z ≅ h_{j Z}`, as a natural
  transformation and as a natural isomorphism of functors `C/V ⥤ PSh(C/U)`.
* `CategoryTheory.OverShriek.relocalizeTerminalIso`: `Λ` of a terminal presheaf is `h_{(V, f)}`.
* `CategoryTheory.OverShriek.relocalizeYonedaFactorIso`: a factorization `ψ ≫ f = W.hom` of the
  structure morphism of `W : C/U` presents `h_W` as `Λ h_{(W.left, ψ)}`.

## Main results

* `CategoryTheory.Over.preservesLimitsOfShape_map_of_isConnected`: `Over.map h` preserves limits
  of every connected shape.
* `CategoryTheory.OverShriek.preservesLimitsOfShape_relocalizePresheafFunctor`: `Λ` preserves
  limits of every connected shape, in particular fibre products.
* `CategoryTheory.OverShriek.isPullback_map_relocalize`: `Λ` carries a cartesian square whose
  lower right corner is representable to a cartesian square with lower right corner `h_{j Z}`.
* `CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`: a morphism
  `h_W ⟶ Λ G` is `Λ σ` for a morphism `σ : h_{(W.left, ψ)} ⟶ G`, read through
  `relocalizeYonedaFactorIso`.
* `CategoryTheory.OverShriek.isPullback_map_relocalize_of_factor`: a represented base change of
  `Λ p` is `Λ` of a represented base change of `p`.
* `CategoryTheory.OverShriek.presheaf_map_relocalize` and
  `CategoryTheory.OverShriek.presheaf_of_presheaf_map_relocalize`: the morphism property
  `P.presheaf` transported across `Λ`, in both directions.
* `CategoryTheory.OverShriek.relocalize_map_diagonal`: `Λ` of a relative diagonal is the relative
  diagonal of `Λ`.

## Implementation notes

No declaration here carries a `@[stacks]` tag.  The two facts are the relocalization analogues of
Stacks 03HU and Stacks 04BB, whose statements for `j_{U!}` are carried by
`CategoryTheory.OverShriek.overShriekSheafifyYonedaIso` and
`CategoryTheory.OverShriek.preservesLimitsOfShape_of_isConnected`; the source states them for
relocalization only in the fppf setting of Stacks 03I4 (2), about sheaves rather than presheaves.

## References

* [Stacks Project, Tag 03HU](https://stacks.math.columbia.edu/tag/03HU)
* [Stacks Project, Tag 04BB](https://stacks.math.columbia.edu/tag/04BB)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace CategoryTheory

/-- **`Over.map` preserves connected limits.**  Mapping to a larger base and then forgetting the
structure morphism is forgetting the structure morphism, and `Over.forget` both preserves and
reflects limits of a connected shape. -/
instance Over.preservesLimitsOfShape_map_of_isConnected {T : Type u} [Category.{v} T]
    {J : Type w} [Category.{w'} J] [IsConnected J] {X Y : T} (h : X ⟶ Y) :
    PreservesLimitsOfShape J (Over.map h) :=
  have : PreservesLimitsOfShape J (Over.map h ⋙ Over.forget Y) :=
    preservesLimitsOfShape_of_natIso (Over.mapForget h).symm
  preservesLimitsOfShape_of_reflects_of_preserves (Over.map h) (Over.forget Y)

namespace OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-! ### `Λ` preserves connected limits -/

/-- The presheaf level form of Stacks 00Y1 is an equivalence, so its functor `Φ_U` preserves
limits. -/
instance isEquivalence_presheafFunctorToOver :
    (presheafFunctorToOver (U := U) (C := C)).IsEquivalence :=
  (presheafEquivalence (U := U)).isEquivalence_functor

/-- The inverse `Φ_U^{-1} = (F, φ) ↦ F_φ` of the presheaf level form of Stacks 00Y1 preserves
limits. -/
instance isEquivalence_fiberFunctor_id :
    (fiberFunctor (𝟙 (yoneda.obj U)) (C := C)).IsEquivalence :=
  (presheafEquivalence (U := U)).isEquivalence_inverse

/-- **`Λ` commutes with limits of every connected shape**, in particular with fibre products
(`J = WalkingCospan`) and with equalizers (`J = WalkingParallelPair`).

`Λ` is `Φ_V` followed by `Over.map h_f` followed by `Φ_U^{-1}`; the two equivalences preserve all
limits and `Over.map` preserves the connected ones.  This is the relocalization analogue, at the
presheaf level, of Stacks 04BB, proved the same way.  It fails for non-connected shapes: `Λ` does
not preserve the terminal presheaf, by `relocalizeTerminalIso`. -/
instance preservesLimitsOfShape_relocalizePresheafFunctor
    {J : Type w} [Category.{w'} J] [IsConnected J] :
    PreservesLimitsOfShape J (relocalizePresheafFunctor f) :=
  inferInstanceAs (PreservesLimitsOfShape J
    (presheafFunctorToOver ⋙ Over.map (yoneda.map f) ⋙ fiberFunctor (𝟙 (yoneda.obj U))))

/-! ### `Λ` of a representable presheaf -/

/-- **The comparison `Λ h_Z ⟶ h_{j Z}`.**  A section of `Λ h_Z` over `(W --a--> U)` is a pair
`(ψ, s)` with `ψ ≫ f = a` and `s : (W --ψ--> V) ⟶ Z`; it is sent to the morphism
`(W --a--> U) ⟶ j Z` of `C/U` with the same underlying morphism `s.left : W ⟶ Z.left` of `C`. -/
def relocalizeYonedaHom :
    yoneda ⋙ relocalizePresheafFunctor f ⟶ Over.map f ⋙ yoneda where
  app Z :=
    { app := fun W => ↾fun p => Over.homMk p.val.snd.left
        ((Category.assoc p.val.snd.left Z.hom f).symm.trans
          ((congrArg (fun t => t ≫ f) (Over.w p.val.snd)).trans p.2))
      naturality := fun _ _ _ => by ext p; exact Over.OverMorphism.ext rfl }
  naturality Z Z' k := by ext W p; exact Over.OverMorphism.ext rfl

/-- **The comparison `Λ h_Z ⟶ h_{j Z}` is bijective on sections.**

It is injective because the morphism `s : (W --ψ--> V) ⟶ Z` of `C/V` underlying a section
determines its factorization, `ψ = s.left ≫ Z.hom`; it is surjective because a morphism
`t : W ⟶ j Z` of `C/U` provides the factorization `(t.left ≫ Z.hom) ≫ f = W.hom`. -/
theorem bijective_relocalizeYonedaHom_app_app (Z : Over V) (W : (Over U)ᵒᵖ) :
    Function.Bijective (((relocalizeYonedaHom f).app Z).app W) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨ψ, s⟩, h⟩ ⟨⟨ψ', s'⟩, h'⟩ he
    have hl : s.left = s'.left := congrArg Over.Hom.left he
    have hψ : ψ = ψ' :=
      (Over.w s).symm.trans ((congrArg (fun t => t ≫ Z.hom) hl).trans (Over.w s'))
    subst hψ
    exact Subtype.ext (congrArg (Sigma.mk ψ) (Over.OverMorphism.ext hl))
  · intro t
    refine ⟨⟨⟨t.left ≫ Z.hom, Over.homMk t.left rfl⟩,
      (Category.assoc t.left Z.hom f).trans (Over.w t)⟩, ?_⟩
    exact Over.OverMorphism.ext rfl

/-- A bijective map of sets is an isomorphism. -/
instance isIso_relocalizeYonedaHom_app_app (Z : Over V) (W : (Over U)ᵒᵖ) :
    IsIso (((relocalizeYonedaHom f).app Z).app W) :=
  (isIso_iff_bijective _).2 (bijective_relocalizeYonedaHom_app_app f Z W)

/-- A morphism of presheaves which is bijective on sections is an isomorphism. -/
instance isIso_relocalizeYonedaHom_app (Z : Over V) :
    IsIso ((relocalizeYonedaHom f).app Z) :=
  NatIso.isIso_of_isIso_app _

/-- A natural transformation whose components are isomorphisms is an isomorphism. -/
instance isIso_relocalizeYonedaHom : IsIso (relocalizeYonedaHom f) :=
  NatIso.isIso_of_isIso_app _

/-- **`Λ` carries a representable presheaf to a representable presheaf**: `Λ h_Z ≅ h_{j Z}`,
naturally in `Z`.  This is the presheaf level, general site form of Stacks 03I4 (2), and the
relocalization analogue of Stacks 03HU. -/
noncomputable def relocalizeYonedaIso :
    yoneda ⋙ relocalizePresheafFunctor f ≅ Over.map f ⋙ yoneda :=
  asIso (relocalizeYonedaHom f)

/-- The comparison underlying `relocalizeYonedaIso`.  Not a `simp` lemma: rewriting with it blocks
the `Iso` simp set, which is what computes with `relocalizeYonedaIso`. -/
lemma relocalizeYonedaIso_hom : (relocalizeYonedaIso f).hom = relocalizeYonedaHom f := rfl

/-- **`Λ` of a terminal presheaf is representable by `(V --f--> U)`.**  The terminal presheaf on
`C/V` is `h_{(V --𝟙--> V)}`, whose image under `j = Over.map f` is `(V --f--> U)`.  In particular
`Λ` does not preserve terminal objects. -/
noncomputable def relocalizeTerminalIso {T : (Over V)ᵒᵖ ⥤ Type v} (hT : IsTerminal T) :
    (relocalizePresheafFunctor f).obj T ≅ yoneda.obj (Over.mk f) :=
  (relocalizePresheafFunctor f).mapIso
      (hT.uniqueUpToIso (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal)) ≪≫
    (relocalizeYonedaIso f).app (Over.mk (𝟙 V)) ≪≫
      yoneda.mapIso (Over.isoMk (Iso.refl V) (by simp))

/-- **`Λ` carries a fibre product over a representable presheaf to a fibre product over a
representable presheaf.**  This is the two facts together: `Λ` preserves the cartesian square, and
the comparison identifies its lower right corner with `h_{j Z}`. -/
theorem isPullback_map_relocalize {Z : Over V} {A B P : (Over V)ᵒᵖ ⥤ Type v}
    {p₁ : P ⟶ A} {p₂ : P ⟶ B} {a : A ⟶ yoneda.obj Z} {b : B ⟶ yoneda.obj Z}
    (h : IsPullback p₁ p₂ a b) :
    IsPullback ((relocalizePresheafFunctor f).map p₁) ((relocalizePresheafFunctor f).map p₂)
      ((relocalizePresheafFunctor f).map a ≫ (relocalizeYonedaIso f).hom.app Z)
      ((relocalizePresheafFunctor f).map b ≫ (relocalizeYonedaIso f).hom.app Z) :=
  (h.map (relocalizePresheafFunctor f)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((relocalizeYonedaIso f).app Z) (by simp) (by simp) (by simp) (by simp)

/-! ### Morphisms from a representable presheaf into `Λ G` -/

/-- A factorization `ψ ≫ f = W.hom` of the structure morphism of an object `W` of `C/U` exhibits
`W` as the image under `j = Over.map f` of the object `(W.left --ψ--> V)` of `C/V`. -/
def relocalizeFactorIso {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    W ≅ (Over.map f).obj (Over.mk ψ) :=
  Over.isoMk (Iso.refl W.left) (by simpa using h)

/-- A factorization `ψ ≫ f = W.hom` presents `h_W` as `Λ h_{(W.left, ψ)}`: it identifies `W` with
`j (W.left, ψ)` and `Λ h_{(W.left, ψ)}` with `h_{j (W.left, ψ)}`. -/
noncomputable def relocalizeYonedaFactorIso {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    yoneda.obj W ≅ (relocalizePresheafFunctor f).obj (yoneda.obj (Over.mk ψ)) :=
  yoneda.mapIso (relocalizeFactorIso f h) ≪≫ ((relocalizeYonedaIso f).app (Over.mk ψ)).symm

/-- The morphism `h_W ⟶ Λ h_{(W.left, ψ)}` named by the *tautological* section `(ψ, 𝟙)` of
`Λ h_{(W.left, ψ)}` over `W`.  It is the isomorphism `relocalizeYonedaFactorIso`
(`relocalizeYonedaFactorIso_hom`), in the form in which the Yoneda lemma computes it. -/
noncomputable def relocalizeYonedaFactorHom {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj (yoneda.obj (Over.mk ψ)) :=
  yonedaEquiv.symm ⟨⟨ψ, 𝟙 (Over.mk ψ)⟩, h⟩

/-- The tautological section `(ψ, 𝟙)` is the section named by `relocalizeYonedaFactorHom`. -/
private theorem yonedaEquiv_relocalizeYonedaFactorHom {W : Over U} {ψ : W.left ⟶ V}
    (h : ψ ≫ f = W.hom) :
    yonedaEquiv (relocalizeYonedaFactorHom f h) =
      (⟨⟨ψ, 𝟙 (Over.mk ψ)⟩, h⟩ :
        ((relocalizePresheafFunctor f).obj (yoneda.obj (Over.mk ψ))).obj (op W)) :=
  yonedaEquiv.apply_symm_apply _

/-- The comparison of fact 1 carries the tautological section to the identification of `W` with
`j (W.left, ψ)`: the underlying morphism of `C` of both is the identity of `W.left`. -/
theorem relocalizeYonedaFactorHom_comp {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    relocalizeYonedaFactorHom f h ≫ (relocalizeYonedaHom f).app (Over.mk ψ) =
      yoneda.map (relocalizeFactorIso f h).hom := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_relocalizeYonedaFactorHom]
  exact Over.OverMorphism.ext rfl

/-- `relocalizeYonedaFactorIso` is the tautological section: both become the identification of `W`
with `j (W.left, ψ)` after the comparison of fact 1, which is an isomorphism. -/
theorem relocalizeYonedaFactorIso_hom {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    (relocalizeYonedaFactorIso f h).hom = relocalizeYonedaFactorHom f h := by
  have hinv : (relocalizeYonedaHom f).app (Over.mk ψ) ≫
      ((relocalizeYonedaIso f).app (Over.mk ψ)).inv = 𝟙 _ :=
    ((relocalizeYonedaIso f).app (Over.mk ψ)).hom_inv_id
  rw [relocalizeYonedaFactorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ← relocalizeYonedaFactorHom_comp f h, Category.assoc, hinv]
  exact Category.comp_id _

/-- **Every morphism from a representable presheaf into `Λ G` is `Λ` of a morphism from a
representable presheaf.**  A morphism `h_W ⟶ Λ G` is a section of `Λ G` over `W`, that is a
factorization `ψ ≫ f = W.hom` together with a section of `G` over `(W.left --ψ--> V)`, i.e. a
morphism `σ : h_{(W.left, ψ)} ⟶ G`; and `Λ σ`, read through the presentation
`relocalizeYonedaFactorIso` of `h_W` as `Λ h_{(W.left, ψ)}`, is the morphism one started with.

This is what reduces a represented base change over `Λ G` to a represented base change over `G`:
together with `isPullback_map_relocalize` it says that every such base change of `Λ` of a morphism
is `Λ` of a represented base change, over an object of `C/V` with the same underlying object of
`C`. -/
theorem exists_eq_relocalizeYonedaFactorIso_comp {G : (Over V)ᵒᵖ ⥤ Type v} {W : Over U}
    (g : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    ∃ (ψ : W.left ⟶ V) (h : ψ ≫ f = W.hom) (σ : yoneda.obj (Over.mk ψ) ⟶ G),
      g = (relocalizeYonedaFactorIso f h).hom ≫ (relocalizePresheafFunctor f).map σ := by
  set p := yonedaEquiv g with hp
  refine ⟨p.val.fst, p.2, yonedaEquiv.symm p.val.snd, ?_⟩
  have main : g = relocalizeYonedaFactorHom f p.2 ≫
      (relocalizePresheafFunctor f).map (yonedaEquiv.symm p.val.snd) := by
    refine yonedaEquiv.injective ?_
    have hsigma : (yonedaEquiv.symm p.val.snd).app (op (Over.mk p.val.fst))
          (𝟙 (Over.mk p.val.fst)) = p.val.snd :=
      yonedaEquiv.apply_symm_apply _
    rw [yonedaEquiv_comp, yonedaEquiv_relocalizeYonedaFactorHom, ← hp]
    exact Subtype.ext (congrArg (Sigma.mk p.val.fst) hsigma.symm)
  exact main.trans
    (congrArg (fun t => t ≫ (relocalizePresheafFunctor f).map (yonedaEquiv.symm p.val.snd))
      (relocalizeYonedaFactorIso_hom f p.2).symm)

/-! ### Representable morphisms and their properties

A morphism property `P` of `C` gives the property `P.presheaf` of a morphism of presheaves on `C`:
that it is representable, and that `P` holds for every represented base change of it.  Combining
the two facts, `Λ` carries `P₁.presheaf` to `P₂.presheaf` whenever `P₂` holds for `j k` as soon as
`P₁` holds for `k`, and conversely — the represented base changes of `Λ p` are exactly `Λ` of the
represented base changes of `p`, over objects of `C/V` with the same underlying object of `C`. -/

/-- The inverse of the presentation `relocalizeYonedaFactorIso` of `h_W` as `Λ h_{(W.left, ψ)}`,
in terms of the comparison of fact 1. -/
theorem relocalizeYonedaFactorIso_inv {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) :
    (relocalizeYonedaFactorIso f h).inv =
      (relocalizeYonedaIso f).hom.app (Over.mk ψ) ≫ yoneda.map (relocalizeFactorIso f h).inv := by
  simp [relocalizeYonedaFactorIso]

/-- **A represented base change of `Λ p` is `Λ` of a represented base change of `p`.**  Let
`g : h_W ⟶ Λ B` be `Λ σ` read through the presentation of `h_W` as `Λ h_{(W.left, ψ)}`, as
`exists_eq_relocalizeYonedaFactorIso_comp` provides, and let the represented base change of `p` by
`σ` be given by `fst₀` and `snd₀`.  Then `Λ` of that base change is a base change of `Λ p` by `g`,
its own `snd` being `j snd₀` read through the identification of `W` with `j (W.left, ψ)`.

Both facts are used: `Λ` preserves the cartesian square, and the comparison of fact 1 identifies
its two right hand corners with representables. -/
theorem isPullback_map_relocalize_of_factor {A B : (Over V)ᵒᵖ ⥤ Type v} {p : A ⟶ B}
    {W : Over U} {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) {σ : yoneda.obj (Over.mk ψ) ⟶ B}
    {g : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj B}
    (hg : g = (relocalizeYonedaFactorIso f h).hom ≫ (relocalizePresheafFunctor f).map σ)
    {b : Over V} {snd₀ : b ⟶ Over.mk ψ} {fst₀ : yoneda.obj b ⟶ A}
    (hpb : IsPullback fst₀ (yoneda.map snd₀) p σ) :
    IsPullback (((relocalizeYonedaIso f).app b).inv ≫ (relocalizePresheafFunctor f).map fst₀)
      (yoneda.map ((Over.map f).map snd₀ ≫ (relocalizeFactorIso f h).inv))
      ((relocalizePresheafFunctor f).map p) g := by
  refine (hpb.map (relocalizePresheafFunctor f)).of_iso
    ((relocalizeYonedaIso f).app b) (Iso.refl _) (relocalizeYonedaFactorIso f h).symm
    (Iso.refl _) (by simp) ?_ (by simp) ?_
  · rw [Iso.symm_hom, relocalizeYonedaFactorIso_inv, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun t => t ≫ yoneda.map (relocalizeFactorIso f h).inv)
      ((relocalizeYonedaIso f).hom.naturality snd₀)
  · simp [hg]

/-- **`Λ` carries a representable morphism with property `P₁` to a representable morphism with
property `P₂`**, as soon as `P₂` holds for `j k` whenever `P₁` holds for `k`.

Every morphism `h_W ⟶ Λ B` is `Λ` of a morphism `h_{(W.left, ψ)} ⟶ B`
(`exists_eq_relocalizeYonedaFactorIso_comp`), so a represented base change of `Λ p` is `Λ` of a
represented base change of `p` (`isPullback_map_relocalize_of_factor`); that gives both
representability of `Λ p` and, two base changes of one cospan being isomorphic over it, the
property for an arbitrary represented base change. -/
theorem presheaf_map_relocalize {P₁ : MorphismProperty (Over V)} {P₂ : MorphismProperty (Over U)}
    [P₂.RespectsIso] (hP : ∀ {a b : Over V} (k : a ⟶ b), P₁ k → P₂ ((Over.map f).map k))
    {A B : (Over V)ᵒᵖ ⥤ Type v} {p : A ⟶ B} (hp : MorphismProperty.presheaf P₁ p) :
    MorphismProperty.presheaf P₂ ((relocalizePresheafFunctor f).map p) := by
  refine ⟨fun W g => ?_, fun W b' g fst snd hsq => ?_⟩
  · obtain ⟨ψ, h, σ, hg⟩ := exists_eq_relocalizeYonedaFactorIso_comp f g
    obtain ⟨b, snd₀, fst₀, hpb⟩ := hp.rep σ
    exact ⟨(Over.map f).obj b, (Over.map f).map snd₀ ≫ (relocalizeFactorIso f h).inv, _,
      isPullback_map_relocalize_of_factor f h hg hpb⟩
  · obtain ⟨ψ, h, σ, hg⟩ := exists_eq_relocalizeYonedaFactorIso_comp f g
    obtain ⟨b, snd₀, fst₀, hpb⟩ := hp.rep σ
    have hsq₂ := isPullback_map_relocalize_of_factor f h hg hpb
    have hsnd : (yoneda.preimageIso (hsq.isoIsPullback _ _ hsq₂)).hom ≫
        ((Over.map f).map snd₀ ≫ (relocalizeFactorIso f h).inv) = snd := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact hsq.isoIsPullback_hom_snd _ _ hsq₂
    rw [← hsnd, P₂.cancel_left_of_respectsIso, P₂.cancel_right_of_respectsIso]
    exact hP snd₀ (hp.property σ fst₀ snd₀ hpb)

/-- **Conversely, a representable morphism whose image under `Λ` has property `P₂` has property
`P₁`**, as soon as `P₁` holds for `k` whenever `P₂` holds for `j k`.

A represented base change of `p` by `σ : h_a ⟶ B` becomes, under `Λ`, a represented base change of
`Λ p` by `Λ σ` whose `snd` is `j snd₀` up to isomorphism, so the hypothesis applies to it.
Representability of `p` is assumed rather than deduced: it is what the consumer has about the
morphism it starts from, and `Λ` does not visibly reflect it. -/
theorem presheaf_of_presheaf_map_relocalize
    {P₁ : MorphismProperty (Over V)} {P₂ : MorphismProperty (Over U)} [P₂.RespectsIso]
    (hP : ∀ {a b : Over V} (k : a ⟶ b), P₂ ((Over.map f).map k) → P₁ k)
    {A B : (Over V)ᵒᵖ ⥤ Type v} {p : A ⟶ B} (hrep : yoneda.relativelyRepresentable p)
    (hp : MorphismProperty.presheaf P₂ ((relocalizePresheafFunctor f).map p)) :
    MorphismProperty.presheaf P₁ p := by
  refine ⟨hrep, fun a b σ fst snd hsq => ?_⟩
  have h : (a.hom : a.left ⟶ V) ≫ f = ((Over.map f).obj a).hom := rfl
  have key := hp.property _ _ _ (isPullback_map_relocalize_of_factor f
    (W := (Over.map f).obj a) (ψ := a.hom) h (σ := σ) (snd₀ := snd) (fst₀ := fst) rfl hsq)
  exact hP snd ((P₂.cancel_right_of_respectsIso _ _).1 key)

/-- **`Λ` of a relative diagonal is the relative diagonal of `Λ`**, read through the comparison
isomorphism which fact 2 provides.  Both sides have the same two components, `Λ` of the identity
and the identity. -/
theorem relocalize_map_diagonal {A B : (Over V)ᵒᵖ ⥤ Type v} (p : A ⟶ B) :
    (relocalizePresheafFunctor f).map (pullback.diagonal p) ≫
        (PreservesPullback.iso (relocalizePresheafFunctor f) p p).hom =
      pullback.diagonal ((relocalizePresheafFunctor f).map p) := by
  refine pullback.hom_ext ?_ ?_ <;> simp [← Functor.map_comp]

end OverShriek

end CategoryTheory

end
