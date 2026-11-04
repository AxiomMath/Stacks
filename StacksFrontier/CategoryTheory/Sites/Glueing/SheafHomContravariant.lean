module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Yoneda
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal hom of sheaves of sets, contravariantly in its source

For a sheaf of sets `G` on a small site `(C, J)` the internal hom `SheafHom(G, -)` is right
adjoint to `G × -`; this is `CategoryTheory.SheafHomAdj.prodSheafHomAdjunction`. This file makes
`SheafHom` a functor of its *source* as well: a morphism `g : G ⟶ G'` is sent to the conjugate,
under the two adjunctions, of the natural transformation `g × - : G × - ⟶ G' × -`, giving
`SheafHom(G', -) ⟶ SheafHom(G, -)`. Assembling these gives the internal hom as a bifunctor
`SheafHom : Sh(C)ᵒᵖ ⥤ Sh(C) ⥤ Sh(C)` and, for a fixed target `F`, the contravariant functor
`SheafHom(-, F) : Sh(C)ᵒᵖ ⥤ Sh(C)`.

The contravariant functor preserves all limits, i.e. it turns a colimit of sheaves in its source
into a limit. Indeed, maps `X ⟶ SheafHom(G, F)` are maps `G × X ⟶ F` naturally in `G`, the
functor `- × X` is a left adjoint and hence preserves colimits, and `Hom(-, F)` turns colimits
into limits; so each corepresentable functor `Hom(X, -)` composed with `SheafHom(-, F)` preserves
limits, and the corepresentable functors jointly reflect them. In particular `SheafHom(-, F)`
carries a coequalizer `A ⇉ B → Q` of sheaves to an equalizer
`SheafHom(Q, F) → SheafHom(B, F) ⇉ SheafHom(A, F)`.

## Main results

* `CategoryTheory.SheafHomAdj.sheafHomContraMap`: the action of `SheafHom(-, F)` on a morphism
  of the source.
* `CategoryTheory.SheafHomAdj.sheafHomBifunctor` and
  `CategoryTheory.SheafHomAdj.sheafHomContra`: the internal hom as a bifunctor, and as a
  contravariant functor for a fixed target.
* `CategoryTheory.SheafHomAdj.sheafHomFunctorTerminalIso`: the internal hom out of a terminal
  sheaf of sets is the identity functor.
* `CategoryTheory.SheafHomAdj.prodFlipSheafHomAdjunction`: `- × X` is left adjoint to
  `SheafHom(X, -)`.
* `CategoryTheory.SheafHomAdj.sheafHomContraCoyonedaIso`: the hom-set description
  `Hom(X, SheafHom(-, F)) ≅ Hom(- × X, F)`.
* `CategoryTheory.SheafHomAdj.preservesLimits_sheafHomContra`: `SheafHom(-, F)` preserves
  limits.
* `CategoryTheory.SheafHomAdj.isLimitForkSheafHomContraMap`: `SheafHom(-, F)` turns a
  coequalizer into an equalizer.

## Implementation notes

Functoriality in the source is obtained from `CategoryTheory.conjugateEquiv`, the bijection
between natural transformations of left adjoints and natural transformations of their right
adjoints. Identities and composites then come from `conjugateEquiv_id` and
`conjugateEquiv_comp`, so no computation with sections of `SheafHom` is needed anywhere in this
file.

The cofork-to-fork statement is proved from the adjunctions rather than from the general
limit-preservation result, because the adjoint description identifies the fork with the image of
the coequalizer under `- × s.pt` for the vertex `s.pt` of a competing fork, which is where the
mathematical content sits.

## References

* [Stacks Project, Tag 0BWQ](https://stacks.math.columbia.edu/tag/0BWQ)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe t w u

namespace CategoryTheory.SheafHomAdj

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The action of the internal hom on a morphism of its source: for `g : G ⟶ G'` the conjugate,
under the two internal-hom adjunctions, of `g × - : G × - ⟶ G' × -`. -/
def sheafHomContraMap {G G' : Sheaf J (Type u)} (g : G ⟶ G') :
    sheafHomFunctor G' ⟶ sheafHomFunctor G :=
  conjugateEquiv (prodSheafHomAdjunction G') (prodSheafHomAdjunction G) (prod.functor.map g)

/-- The internal-hom adjunctions are compatible with the action of `SheafHom` on a morphism
`g : G ⟶ G'` of its source: precomposing a map `G' × W ⟶ F` with `g × W` corresponds to
postcomposing the associated map `W ⟶ SheafHom(G', F)` with `SheafHom(g, F)`. -/
lemma homEquiv_comp_sheafHomContraMap {G G' : Sheaf J (Type u)} (g : G ⟶ G')
    (F W : Sheaf J (Type u)) (φ : (prod.functor.obj G').obj W ⟶ F) :
    (prodSheafHomAdjunction G).homEquiv W F ((prod.functor.map g).app W ≫ φ) =
      (prodSheafHomAdjunction G').homEquiv W F φ ≫ (sheafHomContraMap g).app F := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv (prodSheafHomAdjunction G') (prodSheafHomAdjunction G)
      (prod.functor.map g) W]
  simp only [Category.assoc]
  exact congrArg _ ((sheafHomContraMap g).naturality φ).symm

/-- **The internal hom of sheaves of sets as a bifunctor**, contravariant in the source and
covariant in the target. -/
@[sga "3 I 1.7" "more general"]
def sheafHomBifunctor :
    (Sheaf J (Type u))ᵒᵖ ⥤ Sheaf J (Type u) ⥤ Sheaf J (Type u) where
  obj G := sheafHomFunctor G.unop
  map g := sheafHomContraMap g.unop
  map_id G := by
    simp only [sheafHomContraMap, unop_id, Functor.map_id]
    exact conjugateEquiv_id _
  map_comp g h := by
    simp only [sheafHomContraMap, unop_comp, Functor.map_comp]
    exact (conjugateEquiv_comp _ _ _ _ _).symm

/-- `SheafHom(-, F)` sends the identity of `G` to the identity of `SheafHom(G, -)`. -/
@[simp]
lemma sheafHomContraMap_id (G : Sheaf J (Type u)) :
    sheafHomContraMap (𝟙 G) = 𝟙 (sheafHomFunctor G) :=
  sheafHomBifunctor.map_id (op G)

/-- `SheafHom(-, F)` reverses composition: `SheafHom(h₁ ≫ h₂, -)` is
`SheafHom(h₂, -) ≫ SheafHom(h₁, -)`. -/
lemma sheafHomContraMap_comp {G₁ G₂ G₃ : Sheaf J (Type u)} (h₁ : G₁ ⟶ G₂) (h₂ : G₂ ⟶ G₃) :
    sheafHomContraMap (h₁ ≫ h₂) = sheafHomContraMap h₂ ≫ sheafHomContraMap h₁ :=
  sheafHomBifunctor.map_comp (op h₂) (op h₁)

/-- An isomorphism of sources induces an isomorphism of internal-hom functors. -/
def sheafHomFunctorMapIso {G G' : Sheaf J (Type u)} (e : G ≅ G') :
    sheafHomFunctor G ≅ sheafHomFunctor G' :=
  sheafHomBifunctor.mapIso e.symm.op

/-- Taking the product with a terminal sheaf of sets is the identity functor. -/
def prodTerminalIsoId :
    𝟭 (Sheaf J (Type u)) ≅ prod.functor.obj (⊤_ (Sheaf J (Type u))) :=
  NatIso.ofComponents
    (fun F ↦ (CategoryTheory.Limits.prod.leftUnitor (C := Sheaf J (Type u)) F).symm)
    (fun f ↦ (CategoryTheory.Limits.prod.leftUnitor_inv_naturality f).symm)

/-- **The internal hom out of a terminal sheaf of sets is the identity functor**: a map
`G × W ⟶ F` with `G` terminal is a map `W ⟶ F`. A right adjoint is determined up to
isomorphism by its left adjoint, which here is the identity. -/
def sheafHomFunctorTerminalIso :
    sheafHomFunctor (⊤_ (Sheaf J (Type u))) ≅ 𝟭 (Sheaf J (Type u)) :=
  (prodSheafHomAdjunction (⊤_ (Sheaf J (Type u)))).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft prodTerminalIsoId)

/-- **The internal hom `SheafHom(-, F)` with a fixed target**, a contravariant functor on sheaves
of sets. -/
abbrev sheafHomContra (F : Sheaf J (Type u)) :
    (Sheaf J (Type u))ᵒᵖ ⥤ Sheaf J (Type u) :=
  sheafHomBifunctor ⋙ (evaluation (Sheaf J (Type u)) (Sheaf J (Type u))).obj F

/-- **The internal-hom adjunction with the product taken on the other side**: `- × X` is left
adjoint to `SheafHom(X, -)`, by the braiding of the binary product. -/
def prodFlipSheafHomAdjunction (X : Sheaf J (Type u)) :
    prod.functor.flip.obj X ⊣ sheafHomFunctor X :=
  (prodSheafHomAdjunction X).ofNatIsoLeft
    (NatIso.ofComponents (fun G ↦ prod.braiding X G) (fun f ↦ braid_natural (𝟙 X) f))

/-- **The hom-set description of `SheafHom(-, F)`**: maps `X ⟶ SheafHom(G, F)` are maps
`G × X ⟶ F`, naturally in `G`. -/
def sheafHomContraCoyonedaIso (F X : Sheaf J (Type u)) :
    (prod.functor.flip.obj X).op ⋙ yoneda.obj F ≅
      sheafHomContra F ⋙ coyoneda.obj (op X) :=
  NatIso.ofComponents
    (fun G ↦ Equiv.toIso ((prodSheafHomAdjunction G.unop).homEquiv X F))
    (fun g ↦ by
      ext φ
      exact homEquiv_comp_sheafHomContraMap g.unop F X φ)

/-- **`SheafHom(-, F)` preserves limits**, that is, it turns a colimit of sheaves of sets into a
limit.

For each `X` the composition of `SheafHom(-, F)` with the corepresentable functor `Hom(X, -)` is
the composition of `- × X`, which preserves colimits because it is a left adjoint, with
`Hom(-, F)`, which turns colimits into limits; and the corepresentable functors jointly reflect
limits. -/
instance preservesLimits_sheafHomContra (F : Sheaf J (Type u)) :
    PreservesLimitsOfSize.{t, w} (sheafHomContra F) := by
  refine ⟨fun {K} _ ↦ ⟨fun {D} ↦ ⟨fun {c} hc ↦
    ⟨coyonedaJointlyReflectsLimits _ _ (fun X ↦ ?_)⟩⟩⟩⟩
  have hcol : PreservesColimitsOfShape Kᵒᵖ (prod.functor.flip.obj X.unop) :=
    ((prodFlipSheafHomAdjunction X.unop).leftAdjoint_preservesColimits).preservesColimitsOfShape
  have h₁ : PreservesLimitsOfShape K (prod.functor.flip.obj X.unop).op :=
    preservesLimitsOfShape_op K _
  have h₂ : PreservesLimitsOfShape K (sheafHomContra F ⋙ coyoneda.obj X) :=
    preservesLimitsOfShape_of_natIso (sheafHomContraCoyonedaIso F X.unop)
  exact isLimitOfPreserves (sheafHomContra F ⋙ coyoneda.obj X) hc

/-- **`SheafHom(-, F)` turns a coequalizer into an equalizer.** If `h : B ⟶ Q` is a coequalizer
of `f, g : A ⟶ B` then `SheafHom(h, F)` is an equalizer of `SheafHom(f, F)` and
`SheafHom(g, F)`.

A map `W ⟶ SheafHom(B, F)` equalizing `SheafHom(f, F)` and `SheafHom(g, F)` is a map
`B × W ⟶ F` coequalizing `f × W` and `g × W`; since `- × W` is a left adjoint, `h × W` is a
coequalizer of those two maps, so such a map factors uniquely through `Q × W`. -/
def isLimitForkSheafHomContraMap {A B Q : Sheaf J (Type u)} {f g : A ⟶ B} {h : B ⟶ Q}
    (w : f ≫ h = g ≫ h) (hc : IsColimit (Cofork.ofπ h w)) (F : Sheaf J (Type u)) :
    IsLimit (Fork.ofι ((sheafHomContraMap h).app F)
      (show (sheafHomContraMap h).app F ≫ (sheafHomContraMap f).app F =
          (sheafHomContraMap h).app F ≫ (sheafHomContraMap g).app F by
        rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← sheafHomContraMap_comp,
          ← sheafHomContraMap_comp, w]) :
      Fork ((sheafHomContraMap f).app F) ((sheafHomContraMap g).app F)) := by
  refine Fork.IsLimit.mk' _ (fun s ↦ ?_)
  have hpres : PreservesColimitsOfShape WalkingParallelPair (prod.functor.flip.obj s.pt) :=
    ((prodFlipSheafHomAdjunction s.pt).leftAdjoint_preservesColimits).preservesColimitsOfShape
  have hcol := isColimitCoforkMapOfIsColimit (prod.functor.flip.obj s.pt) w hc
  have hψ : (prod.functor.flip.obj s.pt).map f ≫
        ((prodSheafHomAdjunction B).homEquiv s.pt F).symm (Fork.ι s) =
      (prod.functor.flip.obj s.pt).map g ≫
        ((prodSheafHomAdjunction B).homEquiv s.pt F).symm (Fork.ι s) := by
    refine ((prodSheafHomAdjunction A).homEquiv s.pt F).injective ?_
    simp only [Functor.flip_obj_map]
    rw [homEquiv_comp_sheafHomContraMap f F s.pt, homEquiv_comp_sheafHomContraMap g F s.pt,
      Equiv.apply_symm_apply]
    simpa using s.condition
  have hfac : (prod.functor.flip.obj s.pt).map h ≫ hcol.desc (Cofork.ofπ _ hψ) =
      ((prodSheafHomAdjunction B).homEquiv s.pt F).symm (Fork.ι s) := by
    simpa using hcol.fac (Cofork.ofπ _ hψ) WalkingParallelPair.one
  refine ⟨(prodSheafHomAdjunction Q).homEquiv s.pt F (hcol.desc (Cofork.ofπ _ hψ)), ?_, ?_⟩
  · rw [Fork.ι_ofι, ← homEquiv_comp_sheafHomContraMap h F s.pt,
      show (prod.functor.map h).app s.pt = (prod.functor.flip.obj s.pt).map h from rfl, hfac,
      Equiv.apply_symm_apply]
  · intro m hm
    refine ((prodSheafHomAdjunction Q).homEquiv s.pt F).symm.injective ?_
    rw [Equiv.symm_apply_apply]
    refine Cofork.IsColimit.hom_ext hcol ?_
    rw [Cofork.π_ofπ, hfac]
    refine ((prodSheafHomAdjunction B).homEquiv s.pt F).injective ?_
    simp only [Functor.flip_obj_map]
    rw [homEquiv_comp_sheafHomContraMap h F s.pt, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simpa [Fork.ι_ofι] using hm

end CategoryTheory.SheafHomAdj

end
