module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Basic
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Ringed
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Site
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf on a simplicial semi-representable localization

For a simplicial formal coproduct `K` in a site `C`, the total localization has objects
`U ⟶ Kₙ,ᵢ` and the commuting-square morphisms of Stacks 0D8B. Its covering sieves are those
whose arrows in a fixed degree and component cover `U` in `C`.

The localization augmentation is induced by the forgetful functor `j_total` to `C`, which is
both continuous and cocontinuous for these topologies; its inverse image is restriction along
that functor. In particular the pulled-back structure sheaf `a⁻¹ O_C` is the ordinary sheaf of
commutative rings with sections `O_C(U)` over `U ⟶ Kₙ,ᵢ`.

Continuity is the content: a compatible family on a total covering sieve is a compatible family
on the underlying covering sieve of `C`, because every total arrow into a fixed object factors
through the structural arrow that keeps the degree and the component.

## Main definitions

* `CategoryTheory.SemiRepresentable.Simplicial.TotalLocalization`: the total category of the
  simplicial localization, the comma category `(incl C ↓ K)`.
* `CategoryTheory.SemiRepresentable.Simplicial.totalLocalizationTopology`: its topology.
* `CategoryTheory.SemiRepresentable.Simplicial.localizationAugmentation`: the canonical
  morphism of topoi of Stacks 0D8B.
* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackStructureSheaf`: the pulled-back
  structure sheaf `a⁻¹ O_C`, as a sheaf of commutative rings.
* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackRingSheaf`: the same sheaf with
  commutativity forgotten, ready for `SheafOfModules`.
* `CategoryTheory.SemiRepresentable.Simplicial.componentInclusion`: the inclusion of the
  degree-`n` componentwise localization into the total localization.

## Main results

* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackStructureSheaf_obj`: the sections of
  the pulled-back structure sheaf over `U ⟶ Kₙ,ᵢ` are `O_C(U)`.
* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackStructureSheaf_underlying`: forgetting
  the ring operations gives exactly the inverse image under the augmentation.
* `CategoryTheory.SemiRepresentable.Simplicial.componentInclusion_totalLocalizationFunctor`: the
  total localization restricts to the componentwise localization in each degree.
* `CategoryTheory.SemiRepresentable.Simplicial.pulledBackStructureSheaf_component`: in degree `n`
  the pulled-back structure sheaf restricts to the localization structure sheaf of Stacks 0D9U.

## Implementation notes

`pulledBackRingSheaf` forgets commutativity using the existing ringed-site API, so that it can
be passed directly to `SheafOfModules`. The site object, morphism, component-index and ring
universes are independent; only the topos augmentation enlarges its universe of sets, to ensure
the existence of the right Kan extension.

The total category is the comma category `(FormalCoproduct.incl C ↓ K)`, whose structural arrows
are identified with pairs `(i, U ⟶ Kₙ,ᵢ)` by `CategoryTheory.FormalCoproduct.inclHomEquiv`.
`componentInclusion` gives the comparison with the degreewise localizations of Stacks 0D9U.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe x v u w

namespace CategoryTheory.SemiRepresentable.Simplicial

variable {C : Type u} [Category.{v} C]
variable (K : SimplicialObject (FormalCoproduct.{x} C))

/-- The total category of the simplicial localization, with its commuting-square morphisms. -/
abbrev TotalLocalization := Comma (FormalCoproduct.incl C) K

/-- The localization functor `j_total`, forgetting the degree and the structural arrow. -/
abbrev totalLocalizationFunctor : TotalLocalization K ⥤ C := Comma.fst _ _

variable {K}

/-- Pull an object back along an arrow of the original site, keeping its degree and component. -/
def verticalObject (X : TotalLocalization K) {U : C} (f : U ⟶ X.left) : TotalLocalization K :=
  ⟨U, X.right, (FormalCoproduct.incl C).map f ≫ X.hom⟩

/-- The arrow in a fixed degree and component induced by a map of the original site. -/
def verticalArrow (X : TotalLocalization K) {U : C} (f : U ⟶ X.left) : verticalObject X f ⟶ X where
  left := f
  right := 𝟙 _
  w := by simp [verticalObject]

/-- Compare vertical restrictions along a commuting square of underlying arrows. -/
def verticalComparison {X Y : TotalLocalization K} (g : X ⟶ Y) {U V : C}
    (a : U ⟶ X.left) (b : V ⟶ Y.left) (f : U ⟶ V) (h : f ≫ b = a ≫ g.left) :
    verticalObject X a ⟶ verticalObject Y b where
  left := f
  right := g.right
  w := by
    dsimp [verticalObject]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp,
      Category.assoc, g.w, Category.assoc]

/-- The vertical comparison commutes with the structural vertical arrows. -/
lemma verticalComparison_comp {X Y : TotalLocalization K} (g : X ⟶ Y) {U V : C}
    (a : U ⟶ X.left) (b : V ⟶ Y.left) (f : U ⟶ V) (h : f ≫ b = a ≫ g.left) :
    verticalComparison g a b f h ≫ verticalArrow Y b = verticalArrow X a ≫ g := by
  apply Comma.hom_ext
  · exact h
  · simp [verticalComparison, verticalArrow, verticalObject]

/-- Restrict a total sieve to arrows in its target degree and component. -/
def verticalSieve {X : TotalLocalization K} (S : Sieve X) : Sieve X.left where
  arrows U f := S (verticalArrow X f)
  downward_closed := by
    intro U V f hf g
    let h := verticalComparison (𝟙 X) (g ≫ f) f g (by simp)
    have hh : h ≫ verticalArrow X f = verticalArrow X (g ≫ f) := by
      simpa using verticalComparison_comp (𝟙 X) (g ≫ f) f g (by simp)
    exact hh ▸ S.downward_closed hf h

/-- Base change of a vertical covering refines the vertical part of the total base change. -/
lemma verticalSieve_pullback_le {X Y : TotalLocalization K} (S : Sieve Y) (f : X ⟶ Y) :
    (verticalSieve S).pullback f.left ≤ verticalSieve (S.pullback f) := by
  intro U g hg
  have hh := S.downward_closed hg (verticalComparison f g (g ≫ f.left) (𝟙 U) (by simp))
  rwa [verticalComparison_comp] at hh

/-- Vertical base change is detected on the underlying site. -/
lemma verticalSieve_pullback_verticalArrow_le {X : TotalLocalization K} (S : Sieve X)
    {U : C} (f : U ⟶ X.left) :
    verticalSieve (S.pullback (verticalArrow X f)) ≤ (verticalSieve S).pullback f := by
  intro V g hg
  let a : verticalObject X (g ≫ f) ⟶ verticalObject (verticalObject X f) g :=
    { left := 𝟙 V
      right := 𝟙 X.right
      w := by
        simp only [verticalObject, CategoryTheory.Functor.map_id, Category.id_comp,
          K.map_id, Category.comp_id]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ X.hom) ((FormalCoproduct.incl C).map_comp g f).symm) }
  have hh : a ≫ verticalArrow (verticalObject X f) g ≫ verticalArrow X f =
      verticalArrow X (g ≫ f) := by
    apply Comma.hom_ext <;> simp [a, verticalArrow, verticalObject]
  show S (verticalArrow X (g ≫ f))
  rw [← hh]
  exact S.downward_closed hg a

variable (J : GrothendieckTopology C) (K)

/-- A total sieve covers precisely when its vertical arrows cover in the original site. -/
def totalLocalizationTopology : GrothendieckTopology (TotalLocalization K) where
  sieves X := {S | verticalSieve S ∈ J X.left}
  top_mem' X := J.top_mem X.left
  pullback_stable' := by
    intro X Y S f hS
    exact J.superset_covering (verticalSieve_pullback_le S f) (J.pullback_stable f.left hS)
  transitive' := by
    intro X S hS R hR
    exact J.transitive hS _ fun U f hf =>
      J.superset_covering (verticalSieve_pullback_verticalArrow_le R f) (hR hf)

/-- Restriction along `j_total` sends sheaves to sheaves. -/
instance totalLocalizationFunctor_isContinuous :
    (totalLocalizationFunctor K).IsContinuous (totalLocalizationTopology K J) J where
  op_comp_isSheaf_of_types G X S hS x hx := by
    have hG := (isSheaf_iff_isSheaf_of_type J G.obj).mp G.property
    let y : Presieve.FamilyOfElements G.obj (verticalSieve S).arrows :=
      fun U f hf => x (verticalArrow X f) hf
    have hy : y.Compatible := by
      intro U V W a b f g hf hg h
      let a' := verticalComparison (𝟙 X) (a ≫ f) f a (by simp)
      let b' := verticalComparison (𝟙 X) (a ≫ f) g b (by simpa using h.symm)
      exact hx a' b' hf hg (by
        apply Comma.hom_ext
        · exact h
        · simp [a', b', verticalComparison, verticalArrow, verticalObject])
    obtain ⟨t, ht, hut⟩ := hG (verticalSieve S) hS y hy
    refine ⟨t, ?_, ?_⟩
    · intro Y f hf
      apply (hG.isSeparated _ (J.pullback_stable f.left hS)).ext
      intro U g hg
      have hh := hx (verticalArrow Y g)
        (verticalComparison f g (g ≫ f.left) (𝟙 U) (by simp)) hf hg
        (verticalComparison_comp f g (g ≫ f.left) (𝟙 U) (by simp)).symm
      change G.obj.map g.op (G.obj.map f.left.op t) = G.obj.map g.op (x f hf)
      change G.obj.map g.op (x f hf) = G.obj.map (𝟙 U).op (y (g ≫ f.left) hg) at hh
      rw [op_id, G.obj.map_id (op U)] at hh
      rw [← CategoryTheory.Functor.map_comp_apply]
      exact (ht (g ≫ f.left) hg).trans hh.symm
    · intro t' ht'
      exact hut t' fun U f hf => ht' (verticalArrow X f) hf

/-- A covering of the underlying object lifts in its fixed degree and component. -/
instance totalLocalizationFunctor_isCocontinuous :
    (totalLocalizationFunctor K).IsCocontinuous (totalLocalizationTopology K J) J where
  cover_lift hS := hS

/-- Include the degree-`n` componentwise localization in the total localization. -/
def componentInclusion (n : SimplexCategory) :
    ComponentOver (K.obj (op n)) ⥤ TotalLocalization K :=
  CategoryTheory.Sigma.desc fun i =>
    { obj := fun U => ⟨U.left, op n, FormalCoproduct.Hom.fromIncl i U.hom⟩
      map := fun {U V} g =>
        { left := g.left
          right := 𝟙 _
          w := by
            rw [K.map_id, Category.comp_id]
            refine FormalCoproduct.hom_ext ?_ ?_
            · rfl
            · intro j
              have h : ((FormalCoproduct.incl C).map g.left ≫
                  FormalCoproduct.Hom.fromIncl i V.hom).φ j = g.left ≫ V.hom := rfl
              have h2 : (FormalCoproduct.Hom.fromIncl i U.hom).φ j = U.hom := rfl
              rw [h, h2, Over.w g]
              exact Category.comp_id _ }
      map_id := fun U => by apply Comma.hom_ext <;> rfl
      map_comp := fun f g => by
        apply Comma.hom_ext
        · rfl
        · simp }

/-- The total localization restricts to the usual componentwise localization in each degree. -/
lemma componentInclusion_totalLocalizationFunctor (n : SimplexCategory) :
    componentInclusion K n ⋙ totalLocalizationFunctor K =
      CategoryTheory.Sigma.desc (fun i : (K.obj (op n)).I =>
        Over.forget ((K.obj (op n)).obj i)) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y f
  cases f
  exact HEq.refl _

/-- The canonical localization augmentation of Stacks 0D8B; its inverse image is restriction. -/
def localizationAugmentation :
    MorphismOfTopoi (Sheaf (totalLocalizationTopology K J) (Type max x u v w))
      (Sheaf J (Type max x u v w)) where
  inverseImage := (totalLocalizationFunctor K).sheafPushforwardContinuous
    _ (totalLocalizationTopology K J) J
  pushforward := (totalLocalizationFunctor K).sheafPushforwardCocontinuous
    _ (totalLocalizationTopology K J) J
  adj := (totalLocalizationFunctor K).sheafAdjunctionCocontinuous
    _ (totalLocalizationTopology K J) J
  preservesFiniteLimits := by
    let := ((totalLocalizationFunctor K).sheafAdjunctionContinuous (Type max x u v w)
      (totalLocalizationTopology K J) J).rightAdjoint_preservesLimits
    infer_instance

/-- **Stacks 0D9W, pulled-back structure sheaf.** For the canonical localization
augmentation attached to `K`, set `O = a⁻¹ O_C`. This is restriction along `j_total`,
viewed as a sheaf valued in commutative rings. -/
@[stacks 0D9W "pulled_back_structure_sheaf"]
def pulledBackStructureSheaf (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    Sheaf (totalLocalizationTopology K X.J) CommRingCat.{w} :=
  ((totalLocalizationFunctor K).sheafPushforwardContinuous
    CommRingCat.{w} (totalLocalizationTopology K X.J) X.J).obj X.O

/-- The structure sheaf has the source's sections `O_C(U)` on `U ⟶ Kₙ,ᵢ`. -/
@[simp]
lemma pulledBackStructureSheaf_obj (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) (U : TotalLocalization K) :
    (pulledBackStructureSheaf X K).obj.obj (op U) = X.O.obj.obj (op U.left) := rfl

/-- Forgetting the ring operations gives exactly the inverse image under the canonical
localization augmentation. The universe of sections here is large enough for that topos. -/
lemma pulledBackStructureSheaf_underlying
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    (sheafCompose (totalLocalizationTopology K X.J) (forget CommRingCat)).obj
        (pulledBackStructureSheaf X K) =
      (localizationAugmentation.{x, v, u, w} K X.J).inverseImage.obj
        ((sheafCompose X.J (forget CommRingCat)).obj X.O) := rfl

/-- The structure sheaf with commutativity forgotten, ready for `SheafOfModules`. -/
abbrev pulledBackRingSheaf (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    Sheaf (totalLocalizationTopology K X.J) RingCat.{w} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (pulledBackStructureSheaf X K))

/-- The underlying ring presheaf in degree `n` is exactly the localization structure sheaf of
Stacks 0D9U. The universe specialization here is that of the existing degreewise API. -/
lemma pulledBackStructureSheaf_component (X : AlgebraicGeometry.RingedSite.{u, u, u})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) (n : SimplexCategory) :
    (componentInclusion K n).op ⋙ (pulledBackStructureSheaf X K).obj =
      (AlgebraicGeometry.RingedSite.localizationStructureSheaf X (K.obj (op n))).obj := by
  show (componentInclusion K n ⋙ totalLocalizationFunctor K).op ⋙ X.O.obj = _
  rw [componentInclusion_totalLocalizationFunctor]
  rfl

end CategoryTheory.SemiRepresentable.Simplicial

end
