module

public import StacksFrontier.Topology.Simplicial.DiagramSite

/-!
# The total site of an arbitrary diagram of topological spaces

For a diagram `X : A ⥤ TopCat` of topological spaces indexed by an arbitrary category `A`, the
category `Stacks.Topology.Simplicial.DiagramOpen X` has as objects the open subsets of the spaces
`X a`, and as morphisms `U ⟶ V` the maps of indices `α` with `X(α)(U) ⊆ V`. This file makes it a
site in the sense of the source for *every* index category: a covering of `U` is a family of
morphisms `Uᵢ ⟶ U` whose index maps are isomorphisms and such that the images of the `Uᵢ` cover
`U`. When the index category is iso-rigid — in particular for the simplex category and its
opposite, the case of a simplicial space — an isomorphism of indices is an identity, these are
exactly the levelwise open coverings of `Stacks.Topology.Simplicial.DiagramOpen.precoverage`, and
the site is the site `X_Zar` of the source.

## Main definitions

* `Stacks.Topology.Simplicial.DiagramOpen.IsIsoCovering`: a family of arrows with invertible
  index maps whose images cover the target.
* `Stacks.Topology.Simplicial.DiagramOpen.isoPrecoverage`: these families, as a precoverage.

## Main results

* `Stacks.Topology.Simplicial.DiagramOpen.isoPrecoverage_hasIsos`,
  `isoPrecoverage_hasPullbacks`, `isoPrecoverage_isStableUnderBaseChange` and
  `isoPrecoverage_isStableUnderComposition`: the four axioms of a site, for any index category.
* `Stacks.Topology.Simplicial.DiagramOpen.isoPrecoverage_eq_precoverage`: over an iso-rigid index
  category these coverings are the levelwise open coverings.

## Implementation notes

The levelwise coverings of `Stacks.Topology.Simplicial.DiagramOpen.precoverage` (index maps equal
to identities) are not the coverings of a site when the index category has a non-identity
automorphism `α` of some `a`: the arrow `(a, X a) ⟶ (a, X a)` given by `α` is then an isomorphism
whose singleton family is not levelwise. Asking for invertible index maps instead is the weakest
modification that contains the singleton isomorphisms, and it changes nothing over an iso-rigid
index category.

## References

* [Stacks Project, Tag 09VK](https://stacks.math.columbia.edu/tag/09VK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v₁ u₁

namespace Stacks.Topology.Simplicial

namespace DiagramOpen

variable {A : Type u₁} [Category.{v₁} A] {X : A ⥤ TopCat.{u}}

/-- A family of morphisms to `U` is an *iso-covering* when all its index maps are isomorphisms
and the images of the source opens cover the open of `U`. -/
def IsIsoCovering (U : DiagramOpen X) (R : Presieve U) : Prop :=
  (∀ (V : DiagramOpen X) (f : V ⟶ U), R f → IsIso f.base) ∧
    (∀ x ∈ U.toOpens, ∃ (V : DiagramOpen X) (f : V ⟶ U),
      R f ∧ ∃ y ∈ V.toOpens, X.map f.base y = x)

/-- The iso-coverings of a diagram of topological spaces indexed by an arbitrary category. -/
def isoPrecoverage (X : A ⥤ TopCat.{u}) : Precoverage (DiagramOpen X) where
  coverings U := { R | IsIsoCovering U R }

/-- A presieve on `U` belongs to `isoPrecoverage X` exactly when it is an iso-covering. -/
@[simp]
theorem mem_isoPrecoverage {U : DiagramOpen X} {R : Presieve U} :
    R ∈ isoPrecoverage X U ↔ IsIsoCovering U R :=
  Iff.rfl

/-- The index map of an isomorphism of the total site is an isomorphism. -/
theorem isIso_base_of_isIso {U V : DiagramOpen X} (f : U ⟶ V) [IsIso f] : IsIso f.base :=
  ⟨⟨(asIso f).inv.base,
    congrArg (fun k : U ⟶ U ↦ k.base) (asIso f).hom_inv_id,
    congrArg (fun k : V ⟶ V ↦ k.base) (asIso f).inv_hom_id⟩⟩

/-- Over an iso-rigid index category, a morphism of the total site is levelwise exactly when its
index map is an isomorphism. -/
theorem isLevelwise_iff_isIso_base [IsoRigid A] {U V : DiagramOpen X} (f : U ⟶ V) :
    IsLevelwise f ↔ IsIso f.base := by
  constructor
  · rintro ⟨e, he⟩
    rw [he]
    infer_instance
  · intro _
    exact IsoRigid.eq_eqToHom f.base

/-- Over an iso-rigid index category, the iso-coverings are the levelwise open coverings. -/
theorem isoPrecoverage_eq_precoverage [IsoRigid A] (X : A ⥤ TopCat.{u}) :
    isoPrecoverage X = precoverage X := by
  ext U R
  show IsIsoCovering U R ↔ IsCovering U R
  simp only [IsIsoCovering, IsCovering, isLevelwise_iff_isIso_base]

/-- **The identity-covering axiom.** A singleton isomorphism is an iso-covering. -/
instance isoPrecoverage_hasIsos (X : A ⥤ TopCat.{u}) : (isoPrecoverage X).HasIsos := by
  constructor
  intro U V f _
  constructor
  · rintro W g ⟨⟩
    exact isIso_base_of_isIso f
  · intro x hx
    refine ⟨U, f, .mk, X.map (asIso f).inv.base x, Hom.le (asIso f).inv hx, ?_⟩
    rw [← Functor.map_comp_apply, ← Hom.comp_base]
    simp

/-- The open of the explicit pullback of `g : B ⟶ C` along `f : P ⟶ C`, when the index map of
`g` is invertible: the points of `P` whose image, carried back to the index of `B`, lies in
`B`. -/
private noncomputable def pullbackObj {P B C : DiagramOpen X} (f : P ⟶ C) (g : B ⟶ C)
    [IsIso g.base] : DiagramOpen X :=
  ⟨P.index, P.toOpens ⊓ (Opens.map (X.map (f.base ≫ inv g.base))).obj B.toOpens⟩

private lemma hasPullback_of_isIso_base {P B C : DiagramOpen X}
    (f : P ⟶ C) (g : B ⟶ C) [IsIso g.base] : HasPullback g f := by
  let Q := pullbackObj f g
  let p₁ : Q ⟶ B := ⟨f.base ≫ inv g.base, fun _ hx ↦ hx.2⟩
  let p₂ : Q ⟶ P := ⟨𝟙 _, fun x hx ↦ by
    show x ∈ (Opens.map (X.map (𝟙 P.index))).obj P.toOpens
    rw [X.map_id]
    exact hx.1⟩
  have hc : p₁ ≫ g = p₂ ≫ f := by
    apply Hom.ext
    show (f.base ≫ inv g.base) ≫ g.base = 𝟙 _ ≫ f.base
    simp
  refine ⟨⟨PullbackCone.mk p₁ p₂ hc, ?_⟩⟩
  have key : ∀ s : PullbackCone g f, s.snd.base ≫ f.base ≫ inv g.base = s.fst.base := by
    intro s
    have q : s.fst.base ≫ g.base = s.snd.base ≫ f.base := congrArg Hom.base s.condition
    rw [← Category.assoc, ← q]
    simp
  refine PullbackCone.IsLimit.mk hc (fun s ↦ ⟨s.snd.base, fun x hx ↦ ⟨Hom.le s.snd hx, ?_⟩⟩)
    (fun s ↦ Hom.ext _ _ (key s)) (fun s ↦ Hom.ext _ _ (Category.comp_id _))
    (fun s m _ hm₂ ↦ Hom.ext _ _ ((Category.comp_id _).symm.trans (congrArg Hom.base hm₂)))
  show X.map (f.base ≫ inv g.base) (X.map s.snd.base x) ∈ B.toOpens
  rw [← Functor.map_comp_apply, key s]
  exact Hom.le s.fst hx

/-- **Existence of pullbacks.** Pullbacks of arrows of iso-coverings along arbitrary morphisms
exist. -/
instance isoPrecoverage_hasPullbacks (X : A ⥤ TopCat.{u}) : (isoPrecoverage X).HasPullbacks := by
  constructor
  intro P C R f hR
  constructor
  intro B g hg
  have := hR.1 B g hg
  exact hasPullback_of_isIso_base f g

/-- **The base-change axiom.** The base change of an iso-covering along any morphism is an
iso-covering. -/
instance isoPrecoverage_isStableUnderBaseChange (X : A ⥤ TopCat.{u}) :
    (isoPrecoverage X).IsStableUnderBaseChange := by
  constructor
  intro ι S Z f hf T g P p₁ p₂ h
  -- For each `i`, the explicit open of `Y` over which `Z i` maps, and the lift from it to `P i`.
  have lift : ∀ i [IsIso (f i).base],
      ∃ l : (⟨T.index, T.toOpens ⊓ (Opens.map (X.map (g.base ≫ inv (f i).base))).obj
          (Z i).toOpens⟩ : DiagramOpen X) ⟶ P i,
        l.base ≫ (p₁ i).base = 𝟙 _ ∧ (p₁ i).base ≫ l.base = 𝟙 _ := by
    intro i _
    let W : DiagramOpen X :=
      ⟨T.index, T.toOpens ⊓ (Opens.map (X.map (g.base ≫ inv (f i).base))).obj (Z i).toOpens⟩
    let a : W ⟶ T := ⟨𝟙 _, fun x hw ↦ by
      change x ∈ (Opens.map (X.map (𝟙 T.index))).obj T.toOpens
      rw [X.map_id]
      exact hw.1⟩
    let b : W ⟶ Z i := ⟨g.base ≫ inv (f i).base, fun _ hw ↦ hw.2⟩
    have hab : a ≫ g = b ≫ f i := by
      apply Hom.ext
      change 𝟙 _ ≫ g.base = (g.base ≫ inv (f i).base) ≫ (f i).base
      simp
    let l : W ⟶ P i := (h i).lift a b hab
    have hl₁ : l.base ≫ (p₁ i).base = 𝟙 _ := congrArg Hom.base ((h i).lift_fst a b hab)
    have hl₂ : l.base ≫ (p₂ i).base = g.base ≫ inv (f i).base :=
      congrArg Hom.base ((h i).lift_snd a b hab)
    let QP : DiagramOpen X := ⟨(P i).index, ⊥⟩
    let r : QP ⟶ W := ⟨(p₁ i).base, fun _ hx ↦ hx.elim⟩
    let d : QP ⟶ P i := ⟨𝟙 _, fun _ hx ↦ hx.elim⟩
    have hrl : r ≫ l = d := (h i).hom_ext
      (by
        apply Hom.ext
        change ((p₁ i).base ≫ l.base) ≫ (p₁ i).base = 𝟙 _ ≫ (p₁ i).base
        rw [Category.assoc, hl₁, Category.comp_id, Category.id_comp])
      (by
        apply Hom.ext
        have hs : (p₁ i).base ≫ g.base = (p₂ i).base ≫ (f i).base := congrArg Hom.base (h i).w
        change ((p₁ i).base ≫ l.base) ≫ (p₂ i).base = 𝟙 _ ≫ (p₂ i).base
        rw [Category.assoc, hl₂, ← Category.assoc, hs, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id, Category.id_comp])
    exact ⟨l, hl₁, congrArg Hom.base hrl⟩
  constructor
  · rintro Q q ⟨i⟩
    have := hf.1 _ _ (Presieve.ofArrows.mk i)
    obtain ⟨l, hl₁, hl₂⟩ := lift i
    exact ⟨⟨l.base, hl₂, hl₁⟩⟩
  · intro x hx
    obtain ⟨Zi, fi, ⟨i⟩, z, hz, hzmap⟩ := hf.2 (X.map g.base x) (Hom.le g hx)
    have := hf.1 _ _ (Presieve.ofArrows.mk i)
    obtain ⟨l, hl₁, -⟩ := lift i
    have hxW : x ∈ T.toOpens ⊓ (Opens.map (X.map (g.base ≫ inv (f i).base))).obj
        (Z i).toOpens := ⟨hx, by
      change X.map (g.base ≫ inv (f i).base) x ∈ (Z i).toOpens
      rw [Functor.map_comp_apply, ← hzmap, ← Functor.map_comp_apply]
      simpa using hz⟩
    refine ⟨P i, p₁ i, Presieve.ofArrows.mk i, X.map l.base x, Hom.le l hxW, ?_⟩
    rw [← Functor.map_comp_apply, hl₁]
    exact ConcreteCategory.congr_hom (X.map_id _) x

/-- **The composition axiom.** Iso-coverings are stable under composition. -/
instance isoPrecoverage_isStableUnderComposition (X : A ⥤ TopCat.{u}) :
    (isoPrecoverage X).IsStableUnderComposition := by
  constructor
  intro ι S U f hf σ V g hg
  constructor
  · rintro W k ⟨p⟩
    have := (hg p.1).1 _ _ (Presieve.ofArrows.mk p.2)
    have := hf.1 _ _ (Presieve.ofArrows.mk p.1)
    exact inferInstanceAs (IsIso ((g p.1 p.2).base ≫ (f p.1).base))
  · intro x hx
    obtain ⟨Ui, fi, ⟨i⟩, y, hy, rfl⟩ := hf.2 x hx
    obtain ⟨Vj, gj, ⟨j⟩, z, hz, rfl⟩ := (hg i).2 y hy
    exact ⟨V i j, g i j ≫ f i, Presieve.ofArrows.mk (Sigma.mk i j), z, hz,
      Functor.map_comp_apply X (g i j).base (f i).base z⟩

end DiagramOpen

end Stacks.Topology.Simplicial

end
