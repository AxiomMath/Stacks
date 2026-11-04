module

public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.ConeLiftAndBasePushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.GermPullbackSystem
public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystem

/-!
# A limiting cone of abelian sheafed spaces over a limiting cone of the spaces

Let `A` be a system of abelian sheaves over a cofiltered diagram of spectral spaces and let `c₀`
be a cone of the underlying spaces. The cone `A.cone c₀` of abelian sheafed spaces over `A.E` has
vertex `c₀.pt` carrying `colimⱼ pⱼ⁻¹𝒜ⱼ`, the colimit of the germ-model pullback system along the
legs of `c₀`, and it is a limiting cone when `c₀` is.

## Main definitions

* `SpectralDiagram.AbelianSystem.germSystem`: the germ-model pullback system `k ↦ pₖ⁻¹𝒜ₖ` of
  abelian sheaves on `c₀.pt`, with `germCocone` and `isColimitGermCocone` its colimit.
* `SpectralDiagram.AbelianSystem.cone`: the cone over `A.E` with vertex `c₀.pt` carrying
  `colimⱼ pⱼ⁻¹𝒜ⱼ`.
* `SpectralDiagram.AbelianSystem.isLimit`: that cone is a limiting cone when `c₀` is.
* `SpectralDiagram.AbelianSystem.isLimitCone`: a limiting cone over `A.E` lying over a given
  limiting cone `c₀` of the spaces.

## Main results

* `SpectralDiagram.AbelianSystem.mapCone_forget_cone`: the cone lies over `c₀`.
* `SpectralDiagram.AbelianSystem.cone_pt_sheaf` and
  `SpectralDiagram.AbelianSystem.pullSystem_cone`: the sheaf on the vertex is the colimit of the
  germ-model system, and the germ-model system of the cone is the one built over `c₀`.
* `SpectralDiagram.AbelianSystem.coleg_cone`: the `k`-th leg of the comparison cocone of the cone
  is the `k`-th colimit inclusion.
* `SpectralDiagram.AbelianSystem.cone_hom_ext`: a morphism into the vertex is determined by its
  composites with the legs.

## References

* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SpectralLimit Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

universe u

namespace SpectralDiagram

namespace AbelianSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}
  (A : D.AbelianSystem) (c₀ : Cone D.F)

/-! ### The germ-model system over a cone of the spaces -/

/-- The given cone of spaces, read as a cone of abelian sheafed spaces over `A.E` whose vertex
carries the constant sheaf at a terminal object. -/
abbrev baseCone : Cone A.E := constTerminalCone A.E c₀

/-- The germ-model pullback system `k ↦ pₖ⁻¹𝒜ₖ` of abelian sheaves on `c₀.pt`, that is,
`SheafedSpaceLimit.pullSystem` of `A.baseCone c₀`. -/
abbrev germSystem : Jᵒᵖ ⥤ (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} :=
  pullSystem (A.baseCone c₀)

/-- The colimit cocone of the germ-model system. -/
abbrev germCocone : Cocone (A.germSystem c₀) := colimit.cocone (A.germSystem c₀)

/-- `A.germCocone c₀` is a colimit cocone. -/
def isColimitGermCocone : IsColimit (A.germCocone c₀) := colimit.isColimit _

/-- The cone over `A.E` with vertex `c₀.pt` carrying `colimⱼ pⱼ⁻¹𝒜ⱼ`. The `k`-th leg has base map
the `k`-th leg of `c₀` and sheaf component the adjoint of the `k`-th colimit inclusion. -/
def cone : Cone A.E where
  pt := reseat (A.baseCone c₀) (A.germCocone c₀).pt.presheaf (A.germCocone c₀).pt.2
  π :=
    { app := fun k =>
        leg (A.baseCone c₀) (A.germCocone c₀).pt.presheaf (A.germCocone c₀).pt.2 k
          (pushAdj (A.baseCone c₀) (A.germCocone c₀).pt.presheaf k
            ((A.germCocone c₀).ι.app (op k)).hom)
      naturality := fun _ _ a => (Category.id_comp _).trans
        (leg_pushAdj_comp (A.baseCone c₀) (A.germCocone c₀) a).symm }

/-- The base map of the `k`-th leg of `A.cone c₀` is the `k`-th leg of `c₀`. -/
lemma cone_base (k : J) : ((A.cone c₀).π.app k).hom.base = c₀.π.app k := rfl

/-- The forgetful functor to spaces carries `A.cone c₀` to `c₀`. -/
lemma mapCone_forget_cone :
    (SheafedSpace.forget AddCommGrpCat.{u}).mapCone (A.cone c₀) = c₀ := rfl

/-- The sheaf on the vertex of `A.cone c₀` is the colimit of the germ-model system. -/
lemma cone_pt_sheaf : (A.cone c₀).pt.sheaf = colimit (A.germSystem c₀) := rfl

/-- The germ-model pullback system of `A.cone c₀` is the germ-model system built over `c₀`. -/
lemma pullSystem_cone : pullSystem (A.cone c₀) = A.germSystem c₀ := rfl

/-- The `k`-th leg of the comparison cocone of `A.cone c₀` is the `k`-th colimit inclusion. -/
lemma coleg_cone (k : J) :
    coleg (A.cone c₀) k = ((A.germCocone c₀).ι.app (op k)).hom :=
  (GermPullback.mapOut_unique _ _ _ rfl).symm

/-! ### The lift of an arbitrary cone -/

section Lift

variable (hc₀ : IsLimit c₀) (s : Cone A.E)

/-- The base map of the lift of `s`: the lift of the underlying cone of spaces against `c₀`. -/
def liftBase : (s.pt : TopCat.{u}) ⟶ c₀.pt :=
  hc₀.lift ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone s)

/-- The base map of the lift factors the base maps of the legs of `s`. -/
lemma liftBase_comp (k : J) :
    A.liftBase c₀ hc₀ s ≫ c₀.π.app k = (s.π.app k).hom.base :=
  hc₀.fac _ k

/-- The cone `s`, pushed forward along the base map of its lift: the vertex is `c₀.pt` carrying
the pushforward of the sheaf of `s.pt`, and the `k`-th leg is `pushDesc` of the `k`-th leg of `s`
at the base map `c₀.π.app k`. -/
def pushCone : Cone A.E where
  pt := pushSpace s.pt (A.liftBase c₀ hc₀ s)
  π :=
    { app := fun k => pushDesc s.pt (A.liftBase c₀ hc₀ s) (s.π.app k) (c₀.π.app k)
        (A.liftBase_comp c₀ hc₀ s k).symm
      naturality := fun i _ a => (Category.id_comp _).trans
        ((pushDesc_comp s.pt (A.liftBase c₀ hc₀ s) (s.π.app i) (c₀.π.app i)
            (A.liftBase_comp c₀ hc₀ s i).symm (A.E.map a)
            (congrArg (fun m => m ≫ (A.E.map a).hom.base)
              (A.liftBase_comp c₀ hc₀ s i).symm)).trans
          (pushDesc_congr s.pt (A.liftBase c₀ hc₀ s) (s.w a) (c₀.w a) _ _)).symm }

/-- The comparison cocone of `A.pushCone`, read as a cocone on the germ-model system over `c₀`. -/
abbrev pushCocone : Cocone (A.germSystem c₀) := pullCocone (A.pushCone c₀ hc₀ s)

/-- The sheaf half of the lift of `s`: the morphism out of the colimit determined by the
comparison cocone of `A.pushCone`. -/
def liftSheaf : (A.germCocone c₀).pt ⟶ (A.pushCone c₀ hc₀ s).pt.sheaf :=
  (A.isColimitGermCocone c₀).desc (A.pushCocone c₀ hc₀ s)

/-- The sheaf component of the `k`-th leg of `A.cone c₀`, followed by the sheaf half of the lift,
is the sheaf component of the `k`-th leg of `A.pushCone`. -/
lemma pull_liftSheaf (k : J) :
    pull (A.cone c₀) (A.pushCone c₀ hc₀ s).pt.presheaf (A.liftSheaf c₀ hc₀ s).hom k =
      ((A.pushCone c₀ hc₀ s).π.app k).hom.c :=
  have h1 : ((A.germCocone c₀).ι.app (op k)).hom ≫ (A.liftSheaf c₀ hc₀ s).hom =
      coleg (A.pushCone c₀ hc₀ s) k :=
    congrArg (fun m => m.hom)
      ((A.isColimitGermCocone c₀).fac (A.pushCocone c₀ hc₀ s) (op k))
  (Category.assoc _ _ _).trans
    ((congrArg
        (fun t => GermPullback.toPushforwardPresheaf (c₀.π.app k) (A.E.obj k).presheaf ≫ t)
        (((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).map_comp _ _).symm.trans
          (congrArg
            (fun t => (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).map t)
            h1))).trans
      (GermPullback.toPushforwardPresheaf_comp_mapOut (c₀.π.app k)
        (((A.pushCone c₀ hc₀ s).π.app k).hom.c) (A.pushCone c₀ hc₀ s).pt.IsSheaf))

/-- The lift of `s`: the canonical morphism into the pushforward of `s.pt` along the base map of
the lift, followed by the sheaf half of the lift read as a morphism of sheafed spaces with
identity base map. -/
def liftMor : s.pt ⟶ (A.cone c₀).pt :=
  pushMor s.pt (A.liftBase c₀ hc₀ s) ≫
    over (A.cone c₀) (A.pushCone c₀ hc₀ s).pt.presheaf (A.pushCone c₀ hc₀ s).pt.IsSheaf
      (A.liftSheaf c₀ hc₀ s).hom

/-- The lift of `s` followed by the `k`-th leg of `A.cone c₀` is the `k`-th leg of `s`. -/
lemma liftMor_comp (k : J) :
    A.liftMor c₀ hc₀ s ≫ (A.cone c₀).π.app k = s.π.app k :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => pushMor s.pt (A.liftBase c₀ hc₀ s) ≫ t)
        (congrArg
          (fun ψ => leg (A.cone c₀) (A.pushCone c₀ hc₀ s).pt.presheaf
            (A.pushCone c₀ hc₀ s).pt.IsSheaf k ψ)
          (A.pull_liftSheaf c₀ hc₀ s k))).trans
      (pushMor_comp_pushDesc s.pt (A.liftBase c₀ hc₀ s) (s.π.app k) (c₀.π.app k)
        (A.liftBase_comp c₀ hc₀ s k).symm))

include hc₀ in
/-- A morphism into the vertex of `A.cone c₀` is determined by its composites with the legs,
when `c₀` is a limiting cone. -/
lemma cone_hom_ext {m₁ m₂ : s.pt ⟶ (A.cone c₀).pt}
    (h : ∀ k, m₁ ≫ (A.cone c₀).π.app k = m₂ ≫ (A.cone c₀).π.app k) : m₁ = m₂ := by
  have hb : m₁.hom.base = m₂.hom.base :=
    hc₀.hom_ext fun k => congrArg (fun x => x.hom.base) (h k)
  obtain ⟨⟨b₁, δ₁⟩⟩ := m₁
  obtain ⟨⟨b₂, δ₂⟩⟩ := m₂
  have hb' : b₁ = b₂ := hb
  subst hb'
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  have hsh : TopCat.Presheaf.IsSheaf
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} b₁).obj s.pt.presheaf) :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf b₁ s.pt.IsSheaf
  have hcol : ∀ (δ : (A.cone c₀).pt.presheaf ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} b₁).obj s.pt.presheaf) (k : J),
      ((A.germCocone c₀).ι.app (op k)).hom ≫ δ =
        GermPullback.mapOut (c₀.π.app k) (pull (A.cone c₀) _ δ k) hsh := fun δ k => by
    rw [← A.coleg_cone]; exact coleg_comp (A.cone c₀) hsh δ k
  have key : ∀ k : J,
      ((A.germCocone c₀).ι.app (op k)).hom ≫ δ₁ =
        ((A.germCocone c₀).ι.app (op k)).hom ≫ δ₂ := fun k => by
    rw [hcol δ₁ k, hcol δ₂ k]
    exact congrArg (GermPullback.mapOut (c₀.π.app k) · hsh)
      (hom_c_eq (congrArg (fun x => x.hom) (h k)))
  exact congrArg (fun x => x.hom)
    ((A.isColimitGermCocone c₀).hom_ext
      (f := (⟨δ₁⟩ : (A.germCocone c₀).pt ⟶ ⟨_, hsh⟩))
      (f' := (⟨δ₂⟩ : (A.germCocone c₀).pt ⟶ ⟨_, hsh⟩))
      fun j => InducedCategory.hom_ext (key j.unop))

end Lift

/-- `A.cone c₀` is a limiting cone whenever `c₀` is. -/
def isLimit (hc₀ : IsLimit c₀) : IsLimit (A.cone c₀) where
  lift s := A.liftMor c₀ hc₀ s
  fac s k := A.liftMor_comp c₀ hc₀ s k
  uniq s _ hm := A.cone_hom_ext c₀ hc₀ s
    fun k => (hm k).trans (A.liftMor_comp c₀ hc₀ s k).symm

/-- A limiting cone over `A.E` lying over a given limiting cone `c₀` of the spaces; its vertex is
`c₀.pt` carrying `colimⱼ pⱼ⁻¹𝒜ⱼ`. -/
def isLimitCone (hc₀ : IsLimit c₀) :
    Σ' c : Cone A.E, IsLimit c ×'
      ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c = c₀) :=
  ⟨A.cone c₀, A.isLimit c₀ hc₀, A.mapCone_forget_cone c₀⟩

end AbelianSystem

end SpectralDiagram

end
