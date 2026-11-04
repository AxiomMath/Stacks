module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# Relocalization, computed in the slices `Sh(C)/h_U^#`

Let `(C, J)` be a site and let `f : V ⟶ U` be a morphism of `C`.  Stacks 03EH attaches to `f` the
relocalization functor `j = Over.map f : C/V ⥤ C/U`, continuous and cocontinuous, with
`j_{V!} = j_{U!} ∘ j_!`.  Stacks 04IL computes the two functors `j_!` and `j^{-1}` *after* the
identifications `Sh(C/V) = Sh(C)/h_V^#` and `Sh(C/U) = Sh(C)/h_U^#` of Stacks 00Y1: they become

1. `j^{-1}(H --φ--> h_U^#) = (H ×_{φ, h_U^#, h_f^#} h_V^# ⟶ h_V^#)`, base change along `h_f^#`;
2. `j_!(H --φ--> h_V^#) = (H --φ ≫ h_f^#--> h_U^#)`, postcomposition with `h_f^#`.

Here `h_f^#` is `(presheafToSheaf J (Type v)).map (yoneda.map f) : h_V^# ⟶ h_U^#`.

**Which direction of the identification is used.**  Throughout, the identification of Stacks 00Y1
is used in its forward direction, as the functor
`Φ_U := CategoryTheory.OverShriek.sheafFunctorToOver J : Sh(C/U) ⥤ Sh(C)/h_U^#` — the sheaf level
`j_{U!}` viewed as a functor into the slice.  Both statements are isomorphisms of composites in
which `Φ_U` and `Φ_V` appear on one side only, so neither depends on a choice of inverse for the
equivalence: (2) is `j_! ⋙ Φ_U ≅ Φ_V ⋙ Over.map h_f^#` and (1) is
`j^{-1} ⋙ Φ_V ≅ Φ_U ⋙ Over.pullback h_f^#`.

## The proof

Stacks proves (2) first and then deduces (1) "by using that `j^{-1}` is the right adjoint to `j_!`
and that the rule in (1) is the right adjoint to the rule in (2)"; that is exactly the structure
here, `inverseImageCompSheafFunctorToOverIso` being obtained from
`shriekCompSheafFunctorToOverIso` by uniqueness of right adjoints.

Statement (2) is proved at the level of *presheaves*, where the two structural maps to `h_U`
literally agree, and then transported through sheafification.  The presheaf level relocalization
functor is

```
  Λ G = (W --a--> U) ↦ { (ψ, s) | ψ : W ⟶ V, s ∈ G(W --ψ--> V), ψ ≫ f = a } ,
```

which is `presheafFunctorToOver ⋙ Over.map (yoneda.map f) ⋙ fiberFunctor (𝟙 (yoneda.obj U))`:
composing the presheaf level statement (2) with the presheaf level equivalence of Stacks 00Y1
makes it hold *by construction*, and the only thing left to prove about `Λ` is that it is the
presheaf level `j_!`, i.e. that it is left adjoint to restriction along `Over.map f`
(`relocalizeAdjunction`).  Sheafifying that adjunction identifies `Λ` with the sheaf level `j_!`
(`relocalizeSheafifyIso`), and the passage from `Λ` to the slice `Sh(C)/h_U^#` uses that
`Φ_U` does not see the difference between a presheaf and its sheafification
(`sheafifyCompFunctorToOverIso`), which holds because `j_{U!}` inverts `presheafToSheaf` of the
sheafification map and Stacks 03CD identifies `j_{U!}(-^#)` with `(∐-presheaf)^#`.

## Main results

* `CategoryTheory.Over.mapCompPostIso`: `Over.map g ⋙ Over.post F ≅ Over.post F ⋙ Over.map (F g)`.
* `CategoryTheory.OverShriek.relocalizePresheafFunctor`: the presheaf level `j_!`, `Λ` above.
* `CategoryTheory.OverShriek.relocalizeAdjunction`: `Λ` is left adjoint to restriction along
  `Over.map f`, i.e. `Λ` is the presheaf level `j_!`.
* `CategoryTheory.OverShriek.relocalizePresheafFunctorToOverIso`: statement (2) at the presheaf
  level.
* `CategoryTheory.OverShriek.sheafifyCompFunctorToOverIso`: `presheafToSheaf ⋙ Φ_U` agrees with
  the functor `PSh(C/U) ⥤ Sh(C)/h_U^#` given by sheafifying the coproduct presheaf.
* `CategoryTheory.OverShriek.relocalizeSheafifyIso`: `Λ` sheafifies to the sheaf level `j_!`.
* `CategoryTheory.OverShriek.shriekCompSheafFunctorToOverIso` (Stacks 04IL (2)).
* `CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso` (Stacks 04IL (1)).
* `CategoryTheory.OverShriek.homEquiv_symm_inverseImageCompSheafFunctorToOverIso_inv_app`:
  statement (1) is the comparison its counit prescribes, which is what lets it be used in an
  equation transposed across a lower shriek.

Tags covered: 04IL.
-/

@[expose] public section

open CategoryTheory Opposite

universe v v' u u'

namespace CategoryTheory

/-- **`Over.post` commutes with base change along a morphism in the base.**  For `F : D ⥤ E` and
`g : X ⟶ Y` in `D`, both functors send `(T --t--> X)` to `(F T --F t ≫ F g--> F Y)`. -/
def Over.mapCompPostIso {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E] (F : D ⥤ E)
    {X Y : D} (g : X ⟶ Y) :
    Over.map g ⋙ Over.post F ≅ Over.post F ⋙ Over.map (F.map g) :=
  NatIso.ofComponents (fun _ => Over.isoMk (Iso.refl _) (by simp [Over.post]))
    (fun _ => Over.OverMorphism.ext (by simp [Over.post]))

end CategoryTheory

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-! ### The presheaf level relocalization functor and its adjunction -/

/-- **The presheaf level `j_!` for `j = Over.map f`.**  It sends a presheaf `G` on `C/V` to

```
  (W --a--> U) ↦ { (ψ, s) | ψ : W ⟶ V, s ∈ G(W --ψ--> V), ψ ≫ f = a } ,
```

the part of the coproduct presheaf `∐_{ψ : W ⟶ V} G(W --ψ--> V)` of Stacks 03CD lying over `a`.
Presenting it as `presheafFunctorToOver ⋙ Over.map (yoneda.map f) ⋙ fiberFunctor 𝟙` — push `G` to
the coproduct presheaf over `h_V`, view it over `h_U` along `h_f`, and take fibres — is what makes
`relocalizePresheafFunctorToOverIso` hold by construction. -/
def relocalizePresheafFunctor : ((Over V)ᵒᵖ ⥤ Type v) ⥤ ((Over U)ᵒᵖ ⥤ Type v) :=
  presheafFunctorToOver ⋙ Over.map (yoneda.map f) ⋙ fiberFunctor (𝟙 (yoneda.obj U))

/-- Restriction of presheaves along `j = Over.map f`, i.e. the presheaf level `j^{-1}`. -/
abbrev relocalizeRestrict : ((Over U)ᵒᵖ ⥤ Type v) ⥤ ((Over V)ᵒᵖ ⥤ Type v) :=
  (Functor.whiskeringLeft (Over V)ᵒᵖ (Over U)ᵒᵖ (Type v)).obj (Over.map f).op

variable {G : (Over V)ᵒᵖ ⥤ Type v} {F : (Over U)ᵒᵖ ⥤ Type v}

/-- A map `Λ G ⟶ F` restricts to a map `G ⟶ j^{-1}F`: a section `s` of `G` over `(W, ψ)` is the
section `(ψ, s)` of `Λ G` over `(W, ψ ≫ f)`. -/
def relocalizeToRestricted (α : (relocalizePresheafFunctor f).obj G ⟶ F) :
    G ⟶ (relocalizeRestrict f).obj F where
  app W := ↾fun s => α.app (op (Over.mk (W.unop.hom ≫ f))) ⟨⟨W.unop.hom, s⟩, rfl⟩
  naturality W W' g := by
    ext s
    have key : (((relocalizePresheafFunctor f).obj G).map ((Over.map f).op.map g))
        (⟨⟨W.unop.hom, s⟩, rfl⟩ :
          ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (W.unop.hom ≫ f))))
          = ⟨⟨W'.unop.hom, G.map g s⟩, rfl⟩ :=
      Subtype.ext (sigmaMk_eq G s _ g.unop rfl)
    exact (congrArg (fun t => α.app (op (Over.mk (W'.unop.hom ≫ f))) t) key).symm.trans
      (NatTrans.naturality_apply α ((Over.map f).op.map g)
        (⟨⟨W.unop.hom, s⟩, rfl⟩ :
          ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (W.unop.hom ≫ f)))))

/-- Given `β : G ⟶ j^{-1}F`, a factorization `ψ ≫ f = W.hom` and a section `s` of `G` over
`(W.left, ψ)`, the section of `F` over `W` obtained by restricting `β(s)` along the identity of
`W.left`, viewed as a morphism `W ⟶ (W.left, ψ ≫ f)` of `C/U`. -/
def relocalizeDescend (β : G ⟶ (relocalizeRestrict f).obj F) {W : Over U} {ψ : W.left ⟶ V}
    (h : ψ ≫ f = W.hom) (s : G.obj (op (Over.mk ψ))) : F.obj (op W) :=
  F.map (Over.homMk (𝟙 W.left) (by rw [Category.id_comp]; exact h) :
      W ⟶ Over.mk (ψ ≫ f)).op (β.app (op (Over.mk ψ)) s)

/-- `relocalizeDescend` is compatible with restriction along a morphism `m` of `C/U`, the
factorization being transported by composing `ψ` with `m.left`.  This is the naturality of
`relocalizeOfRestricted`, and it comes from the naturality of `β`. -/
lemma relocalizeDescend_map (β : G ⟶ (relocalizeRestrict f).obj F) {W W' : Over U} (m : W' ⟶ W)
    {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) (s : G.obj (op (Over.mk ψ))) :
    F.map m.op (relocalizeDescend f β h s) =
      relocalizeDescend f β (W := W') (ψ := m.left ≫ ψ)
        (by rw [Category.assoc, h]; exact Over.w m)
        (G.map (Over.homMk m.left rfl : Over.mk (m.left ≫ ψ) ⟶ Over.mk ψ).op s) := by
  have hβ : β.app (op (Over.mk (m.left ≫ ψ)))
        (G.map (Over.homMk m.left rfl : Over.mk (m.left ≫ ψ) ⟶ Over.mk ψ).op s)
      = F.map ((Over.map f).map
          (Over.homMk m.left rfl : Over.mk (m.left ≫ ψ) ⟶ Over.mk ψ)).op
        (β.app (op (Over.mk ψ)) s) :=
    NatTrans.naturality_apply β
      (Over.homMk m.left rfl : Over.mk (m.left ≫ ψ) ⟶ Over.mk ψ).op s
  unfold relocalizeDescend
  rw [hβ, ← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, ← op_comp]
  exact congrArg (fun n : W' ⟶ Over.mk (ψ ≫ f) => F.map n.op (β.app (op (Over.mk ψ)) s))
    (Over.OverMorphism.ext (by simp))

/-- A map `G ⟶ j^{-1}F` extends to a map `Λ G ⟶ F`. -/
def relocalizeOfRestricted (β : G ⟶ (relocalizeRestrict f).obj F) :
    (relocalizePresheafFunctor f).obj G ⟶ F where
  app W := ↾fun p => relocalizeDescend f β (W := W.unop) (ψ := p.val.fst) p.2 p.val.snd
  naturality W W' g := by
    ext ⟨⟨ψ, s⟩, hψ⟩
    exact (relocalizeDescend_map f β g.unop (ψ := ψ) hψ s).symm

/-- When the factorization is the tautological one, `relocalizeDescend` restricts along an identity
and therefore does nothing. -/
lemma relocalizeDescend_self (β : G ⟶ (relocalizeRestrict f).obj F) {X : C} (ψ : X ⟶ V)
    (s : G.obj (op (Over.mk ψ))) :
    relocalizeDescend f β (W := Over.mk (ψ ≫ f)) (ψ := ψ) rfl s = β.app (op (Over.mk ψ)) s := by
  unfold relocalizeDescend
  have hid : (Over.homMk (𝟙 (Over.mk (ψ ≫ f)).left)
      (by rw [Category.id_comp]) : Over.mk (ψ ≫ f) ⟶ Over.mk (ψ ≫ f)) = 𝟙 _ :=
    Over.OverMorphism.ext (by simp)
  rw [hid]
  simp

/-- Restricting the extension of `β : G ⟶ j^{-1}F` recovers `β`: on the tautological
factorization `relocalizeDescend` restricts along an identity. -/
lemma relocalizeToRestricted_relocalizeOfRestricted (β : G ⟶ (relocalizeRestrict f).obj F) :
    relocalizeToRestricted f (relocalizeOfRestricted f β) = β := by
  ext W s
  exact relocalizeDescend_self f β W.unop.hom s

/-- Extending the restriction of `α : Λ G ⟶ F` recovers `α`: a section `(ψ, s)` of `Λ G` over
`W` is the restriction along `W ⟶ (W.left, ψ ≫ f)` of the tautological section `(ψ, s)`. -/
lemma relocalizeOfRestricted_relocalizeToRestricted
    (α : (relocalizePresheafFunctor f).obj G ⟶ F) :
    relocalizeOfRestricted f (relocalizeToRestricted f α) = α := by
  ext W ⟨⟨ψ, s⟩, hψ⟩
  have key : ((((relocalizePresheafFunctor f).obj G).map
        (Over.homMk (𝟙 W.unop.left) (by rw [Category.id_comp]; exact hψ) :
          W.unop ⟶ Over.mk (ψ ≫ f)).op)
      (⟨⟨ψ, s⟩, rfl⟩ :
        ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (ψ ≫ f))))) = ⟨⟨ψ, s⟩, hψ⟩ :=
    Subtype.ext (sigmaMk_eq_self G s _ (by simp))
  exact ((NatTrans.naturality_apply α
    (Over.homMk (𝟙 W.unop.left) (by rw [Category.id_comp]; exact hψ) :
      W.unop ⟶ Over.mk (ψ ≫ f)).op
    (⟨⟨ψ, s⟩, rfl⟩ :
      ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (ψ ≫ f))))).symm.trans
      (congrArg (fun t => α.app W t) key))

/-- **`Λ` is the presheaf level `j_!`**: it is left adjoint to restriction along `Over.map f`.

A map `Λ G ⟶ F` is the same thing as a compatible family of maps
`G(W --ψ--> V) → F(W --ψ ≫ f--> U)`, which is a map `G ⟶ j^{-1}F`; that is
`relocalizeToRestricted` and `relocalizeOfRestricted`. -/
def relocalizeAdjunction : relocalizePresheafFunctor f ⊣ relocalizeRestrict f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := relocalizeToRestricted f
          invFun := relocalizeOfRestricted f
          left_inv := relocalizeOfRestricted_relocalizeToRestricted f
          right_inv := relocalizeToRestricted_relocalizeOfRestricted f }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- **Stacks 04IL (2) at the presheaf level.**  The coproduct presheaf of `Λ G`, viewed over `h_U`,
is the coproduct presheaf of `G` viewed over `h_V` and then pushed along `h_f`.  This holds by
construction: `Λ` was defined as `presheafFunctorToOver ⋙ Over.map (yoneda.map f)` followed by the
inverse of `presheafFunctorToOver`, which is the fibre functor
(`CategoryTheory.OverShriek.presheafCounitIso`, part of the presheaf level form of Stacks 00Y1). -/
def relocalizePresheafFunctorToOverIso :
    relocalizePresheafFunctor f ⋙ presheafFunctorToOver (U := U) ≅
      presheafFunctorToOver (U := V) ⋙ Over.map (yoneda.map f) :=
  Functor.isoWhiskerLeft (presheafFunctorToOver (U := V) ⋙ Over.map (yoneda.map f))
      presheafCounitIso ≪≫
    Functor.rightUnitor _

/-! ### Passing to sheaves -/

noncomputable section

variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- The functor `PSh(C/U) ⥤ Sh(C)/h_U^#` sending a presheaf `G` on `C/U` to the sheafification of
its coproduct presheaf, over `h_U^#`.  By construction `sheafFunctorToOver J` is this functor
precomposed with the inclusion of sheaves into presheaves. -/
def presheafFunctorToOverSheafify :
    ((Over U)ᵒᵖ ⥤ Type v) ⥤ Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  presheafFunctorToOver ⋙ Over.post (presheafToSheaf J (Type v))

variable [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- `presheafFunctorToOverSheafify` inverts the sheafification map, on underlying sheaves.

Stacks 03CD identifies `G ↦ (∐-presheaf of G)^#` with `G ↦ j_{U!}(G^#)`
(`CategoryTheory.OverShriek.sheafifyNatIso`).  Under that identification the map in question
becomes `j_{U!}` applied to `presheafToSheaf(toSheafify)`, which is an isomorphism because
`sheafToPresheaf` is fully faithful. -/
instance isIso_presheafToSheaf_map_presheafFunctor_map_toSheafify
    (P : (Over U)ᵒᵖ ⥤ Type v) :
    IsIso ((presheafToSheaf J (Type v)).map
      ((presheafFunctor (U := U)).map (toSheafify (J.over U) P))) := by
  have key : (sheafifyNatIso (U := U) J).hom.app P ≫
      (presheafToSheaf J (Type v)).map ((presheafFunctor (U := U)).map (toSheafify (J.over U) P)) =
      ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          ((presheafToSheaf (J.over U) (Type v)).map (toSheafify (J.over U) P)) ≫
        (sheafifyNatIso (U := U) J).hom.app (sheafify (J.over U) P) :=
    ((sheafifyNatIso (U := U) J).hom.naturality (toSheafify (J.over U) P)).symm
  have : IsIso ((sheafifyNatIso (U := U) J).hom.app P ≫
      (presheafToSheaf J (Type v)).map
        ((presheafFunctor (U := U)).map (toSheafify (J.over U) P))) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_left ((sheafifyNatIso (U := U) J).hom.app P) _

/-- `presheafFunctorToOverSheafify` inverts the sheafification map: an object of `Sh(C)/h_U^#`
does not see the difference between a presheaf on `C/U` and its sheafification.  This is the
previous instance together with the fact that `Over.forget` reflects isomorphisms. -/
instance isIso_presheafFunctorToOverSheafify_map_toSheafify (P : (Over U)ᵒᵖ ⥤ Type v) :
    IsIso ((presheafFunctorToOverSheafify (U := U) J).map (toSheafify (J.over U) P)) := by
  have : IsIso ((Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map
      ((presheafFunctorToOverSheafify (U := U) J).map (toSheafify (J.over U) P))) :=
    isIso_presheafToSheaf_map_presheafFunctor_map_toSheafify J P
  exact isIso_of_reflects_iso _
    (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U)))

/-- The sheafification map, pushed into `Sh(C)/h_U^#`. -/
def sheafifyCompFunctorToOverHom :
    presheafFunctorToOverSheafify (U := U) J ⟶
      presheafToSheaf (J.over U) (Type v) ⋙ sheafFunctorToOver (U := U) J :=
  Functor.whiskerRight (sheafificationAdjunction (J.over U) (Type v)).unit
    (presheafFunctorToOverSheafify (U := U) J)

/-- `sheafifyCompFunctorToOverHom` is an isomorphism, because each of its components is. -/
instance isIso_sheafifyCompFunctorToOverHom :
    IsIso (sheafifyCompFunctorToOverHom (U := U) J) := by
  have : ∀ P, IsIso ((sheafifyCompFunctorToOverHom (U := U) J).app P) := fun P =>
    isIso_presheafFunctorToOverSheafify_map_toSheafify J P
  exact NatIso.isIso_of_isIso_app _

/-- **`Φ_U` does not distinguish a presheaf from its sheafification.**  Composing the
sheafification functor with `Φ_U = sheafFunctorToOver J` gives back
`presheafFunctorToOverSheafify J`, i.e. `(∐-presheaf of G)^#` over `h_U^#`.

This is the bookkeeping that lets a statement proved at the presheaf level be transported to
sheaves. -/
def sheafifyCompFunctorToOverIso :
    presheafToSheaf (J.over U) (Type v) ⋙ sheafFunctorToOver (U := U) J ≅
      presheafFunctorToOverSheafify (U := U) J :=
  (asIso (sheafifyCompFunctorToOverHom (U := U) J)).symm

variable [HasWeakSheafify (J.over V) (Type v)]
  [((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint]

/-- **`Λ` sheafifies to the sheaf level `j_!`.**  Both `Λ ⋙ (-)^#` and `(-)^# ⋙ j_!` are left
adjoint to the same functor `Sh(C/U) ⥤ PSh(C/V)`, namely the underlying presheaf of `j^{-1}`:
the first because `Λ ⊣ j^{-1}` at the presheaf level (`relocalizeAdjunction`) and `(-)^# ⊣ ι`, the
second because `j_! ⊣ j^{-1}` and `(-)^# ⊣ ι`.  That the two right adjoints agree is Mathlib's
`Functor.sheafPushforwardContinuousCompSheafToPresheafIso`. -/
def relocalizeSheafifyIso :
    relocalizePresheafFunctor f ⋙ presheafToSheaf (J.over U) (Type v) ≅
      presheafToSheaf (J.over V) (Type v) ⋙
        (Over.map f).sheafPullback (Type v) (J.over V) (J.over U) :=
  Adjunction.leftAdjointUniq
    ((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v)))
    (((sheafificationAdjunction (J.over V) (Type v)).comp
        ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).ofNatIsoRight
      (Functor.sheafPushforwardContinuousCompSheafToPresheafIso (Over.map f) (Type v)
        (J.over V) (J.over U)))

/-- The presheaf level statement (2), transported to sheaves but before the final bookkeeping:
`(-)^# ⋙ j_! ⋙ Φ_U ≅ (∐-presheaf over h_V^#) ⋙ Over.map h_f^#`. -/
def relocalizeInnerIso :
    (presheafToSheaf (J.over V) (Type v) ⋙
          (Over.map f).sheafPullback (Type v) (J.over V) (J.over U)) ⋙
        sheafFunctorToOver (U := U) J ≅
      presheafFunctorToOverSheafify (U := V) J ⋙
        Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f)) :=
  Functor.isoWhiskerRight (relocalizeSheafifyIso f J).symm (sheafFunctorToOver (U := U) J) ≪≫
    Functor.isoWhiskerLeft (relocalizePresheafFunctor f)
      (sheafifyCompFunctorToOverIso (U := U) J) ≪≫
    Functor.isoWhiskerRight (relocalizePresheafFunctorToOverIso f)
      (Over.post (presheafToSheaf J (Type v))) ≪≫
    Functor.isoWhiskerLeft (presheafFunctorToOver (U := V))
      (Over.mapCompPostIso (presheafToSheaf J (Type v)) (yoneda.map f))

/-- **Stacks 04IL (2).**  Under the identification of Stacks 00Y1, used in the forward direction
`Φ_U = sheafFunctorToOver J : Sh(C/U) ⥤ Sh(C)/h_U^#`, the relocalization lower shriek `j_!` becomes
postcomposition with `h_f^# : h_V^# ⟶ h_U^#`:
```
  j_!(H --φ--> h_V^#) = (H --φ ≫ h_f^#--> h_U^#) .
```

This is Stacks' proof of (2): the identification sends `G` to `j_{V!}G ⟶ j_{V!}(*) = h_V^#`, so
`j_!G` is sent to `j_{U!}j_!G ⟶ j_{U!}(*) = h_U^#`, and `j_{U!}j_! = j_{V!}` — carried out here at
the presheaf level, where the two structural maps to `h_U` are literally the same
(`relocalizePresheafFunctorToOverIso`), and then transported through sheafification. -/
@[stacks 04IL "(2): under the identification of 00Y1, j_! is postcomposition with h_f^#"]
def shriekCompSheafFunctorToOverIso :
    (Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙ sheafFunctorToOver (U := U) J ≅
      sheafFunctorToOver (U := V) J ⋙
        Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f)) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (sheafificationAdjunction (J.over V) (Type v)).counit).symm
      ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙
        sheafFunctorToOver (U := U) J) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (J.over V) (Type v)) (relocalizeInnerIso f J)

variable [J.WEqualsLocallyBijective (Type v)]

/-- The lower shriek statement (2) read through the inverses of the two equivalences:
`Φ_V^{-1} ⋙ j_! ≅ Over.map h_f^# ⋙ Φ_U^{-1}`. -/
def inverseCompShriekRelocalizeIso :
    (sheafEquivalence (U := V) J).inverse ⋙
        (Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ≅
      Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f)) ⋙
        (sheafEquivalence (U := U) J).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivalence (U := U) J).unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sheafEquivalence (U := V) J).inverse
        (shriekCompSheafFunctorToOverIso f J))
      (sheafEquivalence (U := U) J).inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (sheafEquivalence (U := V) J).counitIso
        (Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f))))
      (sheafEquivalence (U := U) J).inverse ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor _) (sheafEquivalence (U := U) J).inverse

/-- **Stacks 04IL (1).**  Under the identification of Stacks 00Y1, used in the forward direction
`Φ_U = sheafFunctorToOver J`, the relocalization inverse image `j^{-1}` becomes base change along
`h_f^# : h_V^# ⟶ h_U^#`:
```
  j^{-1}(H --φ--> h_U^#) = (H ×_{φ, h_U^#, h_f^#} h_V^# ⟶ h_V^#) .
```

This is the proof Stacks suggests: "the reader can now prove (1) by using that `j^{-1}` is the
right adjoint to `j_!` and using that the rule in (1) is the right adjoint to the rule in (2)".
Concretely, `Over.map h_f^# ⋙ Φ_U^{-1}` — which is `j_!` transported, by (2) — is left adjoint both
to `j^{-1} ⋙ Φ_V` and to `Φ_U ⋙ Over.pullback h_f^#`, so the two agree by uniqueness of right
adjoints. -/
@[stacks 04IL "(1): under the identification of 00Y1, j^{-1} is base change along h_f^#"]
def inverseImageCompSheafFunctorToOverIso :
    (Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U) ⋙
        sheafFunctorToOver (U := V) J ≅
      sheafFunctorToOver (U := U) J ⋙
        Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f)) :=
  Adjunction.rightAdjointUniq
    (((sheafEquivalence (U := V) J).symm.toAdjunction.comp
        ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).ofNatIsoLeft
      (inverseCompShriekRelocalizeIso f J))
    ((Over.mapPullbackAdj ((presheafToSheaf J (Type v)).map (yoneda.map f))).comp
      (sheafEquivalence (U := U) J).symm.toAdjunction)

/-- **Stacks 04IL (1) is the comparison its counit prescribes.**  Transposing the inverse of the
comparison across the adjunction `Φ_V^{-1} ⋙ j_! ⊣ j^{-1} ⋙ Φ_V` — the one whose left adjoint
Stacks 04IL (2) identifies with `Over.map h_f^# ⋙ Φ_U^{-1}` — returns, up to that identification,
the counit of base change along `h_f^#` read through Stacks 00Y1 at `U`.

Both sides are morphisms out of `Φ_V^{-1}(Φ_U(j^{-1}... ) ×_{h_U^#} h_V^#)`, and the comparison is
an `Adjunction.rightAdjointUniq`, so this is `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`
for the two adjunctions it is built from, read in the inverse direction by
`Adjunction.rightAdjointUniq_inv_app` and corrected by `Adjunction.ofNatIsoLeft` for the
identification of the two left adjoints.

This is the form in which the comparison enters an equation that has been transposed across a
lower shriek: on one side of such an equation the base change of Stacks 03EH appears, on the
other the relocalization counit, and nothing but this lemma relates them. -/
@[stacks 04IL "(1): the comparison of inverse images is the one its counit prescribes"]
theorem homEquiv_symm_inverseImageCompSheafFunctorToOverIso_inv_app
    (Z : Sheaf (J.over U) (Type v)) :
    (((sheafEquivalence (U := V) J).symm.toAdjunction.comp
          ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).homEquiv
        ((sheafFunctorToOver (U := U) J ⋙
          Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj Z) Z).symm
        ((inverseImageCompSheafFunctorToOverIso f J).inv.app Z) =
      (inverseCompShriekRelocalizeIso f J).hom.app
          ((sheafFunctorToOver (U := U) J ⋙
            Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj Z) ≫
        ((Over.mapPullbackAdj ((presheafToSheaf J (Type v)).map (yoneda.map f))).comp
          (sheafEquivalence (U := U) J).symm.toAdjunction).counit.app Z := by
  refine ((Iso.inv_comp_eq ((inverseCompShriekRelocalizeIso f J).app _)).mp ?_)
  refine Eq.trans (Adjunction.homEquiv_ofNatIsoLeft_symm_apply
      ((sheafEquivalence (U := V) J).symm.toAdjunction.comp
        ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)))
      (inverseCompShriekRelocalizeIso f J)
      ((inverseImageCompSheafFunctorToOverIso f J).inv.app Z)).symm ?_
  refine Eq.trans (congrArg ((((sheafEquivalence (U := V) J).symm.toAdjunction.comp
        ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).ofNatIsoLeft
      (inverseCompShriekRelocalizeIso f J)).homEquiv _ Z).symm
    (Adjunction.rightAdjointUniq_inv_app _ _ Z)) ?_
  exact Adjunction.homEquiv_symm_rightAdjointUniq_hom_app _ _ Z

end

/-- **The structural morphism of `Λ G` over the slice object.**  A section of `Λ G` over
`(W --a--> U)` is a pair `(ψ, s)` with `ψ ≫ f = a`, and this reads off the factorization `ψ`
of `a` through `f`, i.e. the arrow `(W --a--> U) ⟶ (V --f--> U)` of `C/U` that the pair names.
It is the morphism over which `relocalizePresheafFunctor f` is computed as a presheaf on the
slice `C/U` over `h_{Over.mk f}`. -/
def relocalizeStructureMap (G : (Over V)ᵒᵖ ⥤ Type v) :
    (relocalizePresheafFunctor f).obj G ⟶ yoneda.obj (Over.mk f) where
  app _ := ↾fun s => Over.homMk s.1.1 s.2
  naturality _ _ _ := by ext s; rfl

end CategoryTheory.OverShriek
