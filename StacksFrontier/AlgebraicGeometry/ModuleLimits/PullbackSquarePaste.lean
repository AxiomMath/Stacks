module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentStage
/-!
# Pasting the canonical identifications of iterated pullbacks

`StacksFrontier/AlgebraicGeometry/ModuleLimits/MapDescentStage.lean` proves `canHom_comp`, the
pentagon of the pullback pseudofunctor read on
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`: the canonical identification of a pullback along a
composite with the iterated pullback is associative.  This file draws from it the two *pastings*
that a comparison of restrictions of pullbacks needs, and supplies the purely categorical algebra
that turns such a pasting into a statement about conjugated morphisms.

## The categorical half

A natural isomorphism `α : Φ ≅ K ⋙ T` lets a morphism `ξ : K.obj M ⟶ K.obj N` be *conjugated*
into a morphism `Φ.obj M ⟶ Φ.obj N`, namely `α.hom.app M ≫ T.map ξ ≫ α.inv.app N`.  The three
lemmas `conj_shrink_target`, `conj_shrink_source` and `conj_comp` say that this conjugation is
compatible with changing `T`, with changing `K`, and with composing two such situations, *provided*
the comparison isomorphisms fit into a commuting square.  They are stated for bare functors between
bare categories: the whole content of the compatibility is the commuting square, and the rest is
naturality.

## The pullback half

`canHom_paste_target` pastes the pentagon twice: for two factorizations `v ≫ f = s ≫ u` of one
morphism and a further `w` shrinking `v` to `v'` and `s` to `s'`, the comparison of the iterated
pullbacks along the smaller square is the comparison along the larger one followed by the
comparisons for `w`.  `canHom_paste_comp` pastes it three times, for two squares stacked
horizontally.

`pullbackShrinkIso` and `pullbackShrinkSourceIso` are the two comparison isomorphisms built out of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and `canHom` that the conjugation
lemmas are fed.  They are stated for an arbitrary open immersion rather than for
`AlgebraicGeometry.Scheme.Hom.resLE`, which is what makes their component lemmas hold by `rfl`:
with the morphisms abstract the kernel has nothing to unfold, whereas the same statement about a
concrete `resLE` sends it into the definition of the pullback of a sheaf of modules.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_target`,
  `Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_source`,
  `Stacks.AlgebraicGeometry.ModuleLimits.conj_comp`: conjugation by a natural isomorphism is
  compatible with a commuting square of comparisons.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_paste_target`: **the pentagon pasted twice**,
  for a square shrunk on the source side.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_paste_comp`: **the pentagon pasted three times**,
  for two squares pasted horizontally.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v₁ v₂ v₃ v₄ v₅ v₆ w₁ w₂ w₃ w₄ w₅ w₆ u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-! ### Conjugation by a natural isomorphism -/

section Conj

/-- **Changing the second factor.**  Let `α : Φ ≅ K ⋙ T` and `α' : Φ' ≅ K ⋙ T'` be comparisons
with the same first factor `K`, let `G` take `T` to `T'` through `Θ' : T ⋙ G ≅ T'` and `Φ` to `Φ'`
through `Θ : Φ ⋙ G ≅ Φ'`, and assume the resulting square of comparisons commutes.  Then the
conjugate of `ξ` by `α'` is the image under `G` of its conjugate by `α`, read through `Θ`. -/
theorem conj_shrink_target {A : Type w₁} {B : Type w₂} {C : Type w₃} {C' : Type w₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} C']
    (K : A ⥤ B) (T : B ⥤ C) (T' : B ⥤ C') (G : C ⥤ C')
    {Φ : A ⥤ C} {Φ' : A ⥤ C'} (α : Φ ≅ K ⋙ T) (α' : Φ' ≅ K ⋙ T')
    (Θ : Φ ⋙ G ≅ Φ') (Θ' : T ⋙ G ≅ T')
    (h : ∀ P : A, Θ.inv.app P ≫ G.map (α.hom.app P) ≫ Θ'.hom.app (K.obj P) = α'.hom.app P)
    {M N : A} (ξ : K.obj M ⟶ K.obj N) :
    Θ.inv.app M ≫ G.map (α.hom.app M ≫ T.map ξ ≫ α.inv.app N) ≫ Θ.hom.app N =
      α'.hom.app M ≫ T'.map ξ ≫ α'.inv.app N := by
  have eg : G.map (α.hom.app N) ≫ G.map (α.inv.app N) = 𝟙 _ := by
    simp
  have hM : Θ.inv.app M ≫ G.map (α.hom.app M) = α'.hom.app M ≫ Θ'.inv.app (K.obj M) := by
    rw [← h M]
    simp
  have key : α'.inv.app N = Θ'.inv.app (K.obj N) ≫ G.map (α.inv.app N) ≫ Θ.hom.app N := by
    rw [← cancel_epi (α'.hom.app N), Iso.hom_inv_id_app, ← h N]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% eg, Iso.inv_hom_id_app]
  have hnat : Θ'.inv.app (K.obj M) ≫ G.map (T.map ξ) = T'.map ξ ≫ Θ'.inv.app (K.obj N) :=
    (Θ'.inv.naturality ξ).symm
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [key, reassoc_of% hM, reassoc_of% hnat]

/-- **Changing the first factor.**  Let `α : Φ ≅ K ⋙ T` and `α' : Φ ≅ K' ⋙ T'` be comparisons of
the *same* functor `Φ`, let `H` take `K` to `K'` through `Λ : K ⋙ H ≅ K'` and `T'` back to `T`
through `Ω : H ⋙ T' ≅ T`, and assume the resulting square commutes.  Then conjugating by `α'` the
transport of `ξ` along `Λ` gives the conjugate of `ξ` by `α`. -/
theorem conj_shrink_source {A : Type w₁} {B : Type w₂} {B' : Type w₃} {C : Type w₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} B'] [Category.{v₄} C]
    (K : A ⥤ B) (K' : A ⥤ B') (H : B ⥤ B') (T : B ⥤ C) (T' : B' ⥤ C)
    {Φ : A ⥤ C} (α : Φ ≅ K ⋙ T) (α' : Φ ≅ K' ⋙ T')
    (Λ : K ⋙ H ≅ K') (Ω : H ⋙ T' ≅ T)
    (h : ∀ P : A, α'.hom.app P = α.hom.app P ≫ Ω.inv.app (K.obj P) ≫ T'.map (Λ.hom.app P))
    {M N : A} (ξ : K.obj M ⟶ K.obj N) :
    α'.hom.app M ≫ T'.map (Λ.inv.app M ≫ H.map ξ ≫ Λ.hom.app N) ≫ α'.inv.app N =
      α.hom.app M ≫ T.map ξ ≫ α.inv.app N := by
  have e1 : T'.map (Λ.hom.app M) ≫ T'.map (Λ.inv.app M) = 𝟙 _ := by
    simp
  have e2 : T'.map (Λ.hom.app N) ≫ T'.map (Λ.inv.app N) = 𝟙 _ := by
    simp
  have key : α'.inv.app N = T'.map (Λ.inv.app N) ≫ Ω.hom.app (K.obj N) ≫ α.inv.app N := by
    rw [← cancel_epi (α'.hom.app N), Iso.hom_inv_id_app, h N]
    simp only [Category.assoc]
    rw [reassoc_of% e2, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  have hnat : T'.map (H.map ξ) ≫ Ω.hom.app (K.obj N) = Ω.hom.app (K.obj M) ≫ T.map ξ :=
    Ω.hom.naturality ξ
  rw [h M, key]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% e1, reassoc_of% e2, reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- **Composing two situations.**  Let `αg : G ⋙ K₂ ≅ K ⋙ T` and `αf : F ⋙ K₃ ≅ K₂ ⋙ T₂` be
comparisons that can be stacked, let `αfg : FG ⋙ K₃ ≅ K ⋙ T₁₂` be the comparison for the composite
with `Ψ : G ⋙ F ≅ FG` and `Ξ : T ⋙ T₂ ≅ T₁₂`, and assume the resulting square commutes.  Then
conjugating twice is conjugating once for the composite, up to `Ψ`. -/
theorem conj_comp {A : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {B : Type w₄} {C : Type w₅}
    {D : Type w₆} [Category.{v₁} A] [Category.{v₂} A₂] [Category.{v₃} A₃] [Category.{v₄} B]
    [Category.{v₅} C] [Category.{v₆} D]
    (G : A ⥤ A₂) (F : A₂ ⥤ A₃) {FG : A ⥤ A₃}
    (K : A ⥤ B) {K₂ : A₂ ⥤ C} (K₃ : A₃ ⥤ D) (T : B ⥤ C) (T₂ : C ⥤ D) (T₁₂ : B ⥤ D)
    (αg : G ⋙ K₂ ≅ K ⋙ T) (αf : F ⋙ K₃ ≅ K₂ ⋙ T₂) (αfg : FG ⋙ K₃ ≅ K ⋙ T₁₂)
    (Ψ : G ⋙ F ≅ FG) (Ξ : T ⋙ T₂ ≅ T₁₂)
    (h : ∀ P : A, αf.hom.app (G.obj P) ≫ T₂.map (αg.hom.app P) ≫ Ξ.hom.app (K.obj P) =
      K₃.map (Ψ.hom.app P) ≫ αfg.hom.app P)
    {M N : A} (ξ : K.obj M ⟶ K.obj N) :
    (αf.hom.app (G.obj M) ≫ T₂.map (αg.hom.app M ≫ T.map ξ ≫ αg.inv.app N) ≫
        αf.inv.app (G.obj N)) ≫ K₃.map (Ψ.hom.app N) =
      K₃.map (Ψ.hom.app M) ≫ αfg.hom.app M ≫ T₁₂.map ξ ≫ αfg.inv.app N := by
  have eΨ : K₃.map (Ψ.inv.app N) ≫ K₃.map (Ψ.hom.app N) = 𝟙 _ := by
    simp
  have eg2 : T₂.map (αg.hom.app N) ≫ T₂.map (αg.inv.app N) = 𝟙 _ := by
    simp
  have hN' : αfg.hom.app N = K₃.map (Ψ.inv.app N) ≫ αf.hom.app (G.obj N) ≫
      T₂.map (αg.hom.app N) ≫ Ξ.hom.app (K.obj N) := by
    rw [h N, reassoc_of% eΨ]
  have key : Ξ.hom.app (K.obj N) ≫ αfg.inv.app N =
      T₂.map (αg.inv.app N) ≫ αf.inv.app (G.obj N) ≫ K₃.map (Ψ.hom.app N) := by
    have keyinv : αfg.inv.app N = Ξ.inv.app (K.obj N) ≫ T₂.map (αg.inv.app N) ≫
        αf.inv.app (G.obj N) ≫ K₃.map (Ψ.hom.app N) := by
      rw [← cancel_epi (αfg.hom.app N), Iso.hom_inv_id_app, hN']
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [reassoc_of% eg2, Iso.hom_inv_id_app_assoc, eΨ]
      rfl
    rw [keyinv, Iso.hom_inv_id_app_assoc]
  have hnat : T₂.map (T.map ξ) ≫ Ξ.hom.app (K.obj N) = Ξ.hom.app (K.obj M) ≫ T₁₂.map ξ :=
    Ξ.hom.naturality ξ
  rw [← reassoc_of% (h M), ← reassoc_of% hnat, key]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end Conj

/-! ### Reindexing the pullback along an equality of morphisms -/

variable {X Y Z : Scheme.{u}}

/-- `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along the trivial equality acts as the
identity on every module. -/
theorem pullbackCongr_rfl_hom_app (f : X ⟶ Y) (F : Y.Modules) :
    (pullbackCongr (rfl : f = f)).hom.app F = 𝟙 _ := rfl

/-- `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along the reversed equality is the inverse
reindexing. -/
theorem pullbackCongr_symm_hom_app {f g : X ⟶ Y} (h : f = g) (F : Y.Modules) :
    (pullbackCongr h.symm).hom.app F = (pullbackCongr h).inv.app F := rfl

/-- The pentagon `canHom_comp`, solved for the comparison of `q` with the first factor. -/
private theorem canHom_eq_map_canHom_comp_inv {W Z Y X : Scheme.{u}} (q : W ⟶ Z) (g₁ : Z ⟶ Y)
    (g₂ : Y ⟶ X) (qz : W ⟶ Y) (h₁ : q ≫ g₁ = qz) (g : Z ⟶ X) (hg : g₁ ≫ g₂ = g)
    (pi : W ⟶ X) (h₂ : qz ≫ g₂ = pi) (hq : q ≫ g = pi) (M : X.Modules) :
    canHom q g₁ qz h₁ ((pullback g₂).obj M) =
      (pullback q).map (canHom g₁ g₂ g hg M) ≫
        canHom q g pi hq M ≫ (canNatIso qz g₂ pi h₂).inv.app M := by
  have p := canHom_comp q g₁ g₂ qz h₁ g hg pi h₂ hq M
  rw [canNatIso_hom_app] at p
  rw [reassoc_of% p, ← canNatIso_hom_app qz g₂ pi h₂ M, Iso.hom_inv_id_app]
  simp

/-! ### The two pastings of the pentagon -/

/-- **The pentagon pasted twice, shrinking the source of a commuting square.**  Let
`v ≫ f = s ≫ u` be a commuting square and let `w` shrink it, so that `w ≫ v = v'` and
`w ≫ s = s'` and `v' ≫ f = s' ≫ u`.  Then the comparison of the iterated pullbacks for the
smaller square is the comparison for the larger one, pulled back along `w` and followed by the
canonical identifications for `w`.

Both sides are composites of canonical identifications, so this is a coherence of the pullback
pseudofunctor: it is `canHom_comp` for `(w, v, f)` and `canHom_comp` for `(w, s, u)`, the two
pentagons sharing the identification for `w` and the composite `v ≫ f`. -/
theorem canHom_paste_target {V V' U : Scheme.{u}} (f : X ⟶ Y) (u : U ⟶ Y)
    (v : V ⟶ X) (v' : V' ⟶ X) (w : V' ⟶ V) (s : V ⟶ U) (s' : V' ⟶ U)
    (hwv : w ≫ v = v') (hws : w ≫ s = s')
    (h1 : s ≫ u = v ≫ f) (h1' : s' ≫ u = v' ≫ f) (M : Y.Modules) :
    (pullback w).map (canHom v f (v ≫ f) rfl M) ≫
        (pullback w).map ((canNatIso s u (v ≫ f) h1).inv.app M) ≫
        canHom w s s' hws ((pullback u).obj M) =
      canHom w v v' hwv ((pullback f).obj M) ≫
        canHom v' f (v' ≫ f) rfl M ≫ (canNatIso s' u (v' ≫ f) h1').inv.app M := by
  have hq : w ≫ v ≫ f = v' ≫ f := by rw [← Category.assoc, hwv]
  have pA := canHom_comp w v f v' hwv (v ≫ f) rfl (v' ≫ f) rfl hq M
  rw [canNatIso_hom_app] at pA
  have einv : (pullback w).map ((canNatIso s u (v ≫ f) h1).inv.app M) ≫
      (pullback w).map ((canNatIso s u (v ≫ f) h1).hom.app M) = 𝟙 _ := by
    simp
  have hpB := canHom_eq_map_canHom_comp_inv w s u s' hws (v ≫ f) h1 (v' ≫ f) h1' hq M
  rw [hpB, ← canNatIso_hom_app s u (v ≫ f) h1 M, reassoc_of% einv, reassoc_of% pA]

/-- **The pentagon pasted three times, for two commuting squares side by side.**  Let
`sf ≫ u = v ≫ f` and `sg ≫ wι = u ≫ g` be commuting squares and `sf ≫ sg = sfg` the composite
of their lower edges, with `sfg ≫ wι = v ≫ f ≫ g`.  Then the comparison of the iterated
pullbacks for the pasted square is the two comparisons one after the other, up to the canonical
identification of `pullback g ⋙ pullback f` with `pullback (f ≫ g)`.

This is `canHom_comp` for `(sf, sg, wι)`, for `(sf, u, g)` and for `(v, f, g)`. -/
theorem canHom_paste_comp {V U W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : V ⟶ X) (u : U ⟶ Y) (wι : W ⟶ Z) (sf : V ⟶ U) (sg : U ⟶ W) (sfg : V ⟶ W)
    (hf : sf ≫ u = v ≫ f) (hg : sg ≫ wι = u ≫ g) (hfg : sfg ≫ wι = v ≫ f ≫ g)
    (hsf : sf ≫ sg = sfg) (P : Z.Modules) :
    canHom v f (v ≫ f) rfl ((pullback g).obj P) ≫
        (canNatIso sf u (v ≫ f) hf).inv.app ((pullback g).obj P) ≫
        (pullback sf).map (canHom u g (u ≫ g) rfl P) ≫
        (pullback sf).map ((canNatIso sg wι (u ≫ g) hg).inv.app P) ≫
        canHom sf sg sfg hsf ((pullback wι).obj P) =
      (pullback v).map (canHom f g (f ≫ g) rfl P) ≫
        canHom v (f ≫ g) (v ≫ f ≫ g) rfl P ≫
          (canNatIso sfg wι (v ≫ f ≫ g) hfg).inv.app P := by
  have hq1 : sf ≫ u ≫ g = v ≫ f ≫ g := by rw [← Category.assoc, hf, Category.assoc]
  have h2 : (v ≫ f) ≫ g = v ≫ f ≫ g := Category.assoc _ _ _
  have p2 := canHom_comp sf u g (v ≫ f) hf (u ≫ g) rfl (v ≫ f ≫ g) h2 hq1 P
  have p3 := canHom_comp v f g (v ≫ f) rfl (f ≫ g) rfl (v ≫ f ≫ g) h2 rfl P
  simp only [canNatIso_hom_app] at p2 p3
  have hp1 := canHom_eq_map_canHom_comp_inv sf sg wι sfg hsf (u ≫ g) hg (v ≫ f ≫ g) hfg hq1 P
  have ecancel : (pullback sf).map ((canNatIso sg wι (u ≫ g) hg).inv.app P) ≫
      (pullback sf).map (canHom sg wι (u ≫ g) hg P) = 𝟙 _ := by
    rw [← canNatIso_hom_app sg wι (u ≫ g) hg P, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hp1, reassoc_of% ecancel, reassoc_of% p2,
    ← canNatIso_hom_app sf u (v ≫ f) hf ((pullback g).obj P), Iso.inv_hom_id_app_assoc,
    reassoc_of% p3.symm]

/-! ### The two comparison isomorphisms built from the pentagon -/

/-- **Restricting a pullback to a smaller open of its source.**  For an open immersion
`w : V' ⟶ V` and `s : V ⟶ U` with `w ≫ s = s'`, restricting the pullback along `s` along `w` is
the pullback along `s'`.

It is stated for an arbitrary open immersion `w` and arbitrary `s`, `s'` rather than for
`AlgebraicGeometry.Scheme.Hom.resLE`, so that `pullbackShrinkIso_hom_app` holds by `rfl`. -/
noncomputable def pullbackShrinkIso {V V' U : Scheme.{u}} (w : V' ⟶ V) [IsOpenImmersion w]
    (s : V ⟶ U) (s' : V' ⟶ U) (hws : w ≫ s = s') :
    pullback s ⋙ restrictFunctor w ≅ pullback s' :=
  Functor.isoWhiskerLeft (pullback s) (restrictFunctorIsoPullback w) ≪≫ canNatIso w s s' hws

/-- `pullbackShrinkIso` at a single module: the restriction comparison followed by the canonical
identification of the iterated pullback. -/
theorem pullbackShrinkIso_hom_app {V V' U : Scheme.{u}} (w : V' ⟶ V) [IsOpenImmersion w]
    (s : V ⟶ U) (s' : V' ⟶ U) (hws : w ≫ s = s') (Q : U.Modules) :
    (pullbackShrinkIso w s s' hws).hom.app Q =
      (restrictFunctorIsoPullback w).hom.app ((pullback s).obj Q) ≫ canHom w s s' hws Q := rfl

/-- **Pulling a restriction back along a smaller open of its target.**  For an open immersion
`w : U' ⟶ U` and `s' : V ⟶ U'` with `s' ≫ w = s`, pulling the restriction along `w` back along
`s'` is pulling back along `s`.

As with `pullbackShrinkIso`, the morphisms are arbitrary so that
`pullbackShrinkSourceIso_inv_app` holds by `rfl`. -/
noncomputable def pullbackShrinkSourceIso {U U' V : Scheme.{u}} (w : U' ⟶ U)
    [IsOpenImmersion w] (s' : V ⟶ U') (s : V ⟶ U) (hws : s' ≫ w = s) :
    restrictFunctor w ⋙ pullback s' ≅ pullback s :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback w) (pullback s') ≪≫ canNatIso s' w s hws

/-- `pullbackShrinkSourceIso` at a single module, in the inverse direction. -/
theorem pullbackShrinkSourceIso_inv_app {U U' V : Scheme.{u}} (w : U' ⟶ U) [IsOpenImmersion w]
    (s' : V ⟶ U') (s : V ⟶ U) (hws : s' ≫ w = s) (Q : U.Modules) :
    (pullbackShrinkSourceIso w s' s hws).inv.app Q =
      (canNatIso s' w s hws).inv.app Q ≫
        (pullback s').map ((restrictFunctorIsoPullback w).inv.app Q) := rfl

end Stacks.AlgebraicGeometry.ModuleLimits

end
