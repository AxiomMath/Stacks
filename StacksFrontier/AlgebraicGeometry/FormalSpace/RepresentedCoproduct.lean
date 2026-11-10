module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representable coproducts of objects of the big fppf site

A family of objects of the big fppf site over `S` whose coproduct of underlying schemes lies in
the site has a representable coproduct of represented sheaves. More generally, in a site a
covering family of pairwise disjoint monomorphisms exhibits the sheaf represented by its target
as the coproduct of the sheaves its members represent.

## Main results

* `AlgebraicGeometry.FormalSpace.isColimit_represented_disjoint_cover`: the descent statement for
  a covering family of pairwise disjoint monomorphisms.
* `AlgebraicGeometry.FormalSpace.exists_represented_coproduct`: the representable coproduct.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u v w

attribute [local instance] bigFppfOver_subcanonical

/-- A family of monomorphisms of a site which generates a covering sieve and whose members are
pairwise disjoint exhibits the sheaf represented by their common target as the coproduct of the
sheaves they represent. -/
@[sga "4 II 4.6.2" "more general"]
def isColimit_represented_disjoint_cover
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (max u v))]
    {ι : Type w} (V : ι → C) (U : C) (f : ∀ i, V i ⟶ U)
    [∀ i, Mono (f i)] (hcov : Sieve.ofArrows V f ∈ J U)
    (hdisj : ∀ i j, i ≠ j → ∀ (W : C) (a : W ⟶ V i) (b : W ⟶ V j),
      a ≫ f i = b ≫ f j → ⊥ ∈ J W) :
    IsColimit (Cofan.mk ((Sheaf.sheafifiedYoneda J).obj U)
      (fun i => (Sheaf.sheafifiedYoneda J).map (f i))) := by
  classical
  let H := Sheaf.sheafifiedYoneda J
  have he (s : Cofan (fun i => H.obj (V i))) :
      ∃! m : H.obj U ⟶ s.pt, ∀ i, H.map (f i) ≫ m = s.inj i := by
    let x := fun i => Sheaf.sectionEquiv J (s.inj i)
    have hx : Presieve.Arrows.Compatible s.pt.obj f x := by
      intro i j W a b hab
      by_cases hij : i = j
      · subst j
        obtain rfl := (cancel_mono (f i)).mp hab
        rfl
      · let : Unique (s.pt.obj.obj (op W)) := Types.isTerminalEquivUnique _
          (Sheaf.isTerminalOfBotCover s.pt W (hdisj i j hij W a b hab))
        exact Subsingleton.elim _ _
    obtain ⟨t, ht, hu⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
      ((Presieve.isSheafFor_iff_generate _).mpr (s.pt.property.isSheafFor _ hcov)) x hx
    refine ⟨(Sheaf.sectionEquiv J).symm t, fun i => ?_, fun m hm => ?_⟩
    · apply (Sheaf.sectionEquiv J).injective
      rw [Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]
      exact ht i
    · apply (Sheaf.sectionEquiv J).injective
      rw [Equiv.apply_symm_apply]
      exact hu _ fun i => by rw [← Sheaf.sectionEquiv_map_comp, hm]
  exact Cofan.IsColimit.mk _ (fun s => (he s).choose)
    (fun s => (he s).choose_spec.1) (fun s => (he s).choose_spec.2)

/-- The sheaf represented by an object of the big fppf site is the sheafification of its
Yoneda presheaf. -/
def representedSheafIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) :
    (uliftYoneda.{u + 1}).obj T ≅
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T).obj :=
  isoSheafify _ (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf

/-- The empty sieve covers an object of the big fppf site with empty underlying scheme. -/
theorem empty_mem_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj U)] :
    ⊥ ∈ BigFppfOver.topology B S hS U :=
  BigFppfOver.bot_mem_topology_of_isInitial B S hS U <| Over.isInitialOfIsInitialLeft (Y := U)
    (isInitial_schemeBelow B (isInitial_iff_isEmpty.mpr ‹_›).some)

attribute [local instance] sheaf_hasColimits

/-- A family of objects of the big fppf site whose underlying coproduct of schemes again lies
in the site has a representable coproduct of represented sheaves. -/
theorem exists_represented_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Small.{u} I]
    (V : I → BigFppfOver B S hS)
    (hU : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (V i))) :
    ∃ (U : BigFppfOver B S hS)
      (F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))),
      Nonempty (F.obj ≅ (uliftYoneda.{u + 1}).obj U) ∧
      Nonempty (F ≅ ∐ fun i =>
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (V i)) := by
  let W := fun i => (BigFppfOver.toScheme B S hS).obj (V i)
  let U : BigFppfOver B S hS := Over.mk
    (show B.obj hU ⟶ B.obj hS from
      ObjectProperty.homMk (Sigma.desc (fun i => (V i).hom.hom)))
  let f : ∀ i, V i ⟶ U := fun i => Over.homMk
    (ObjectProperty.homMk (Sigma.ι W i))
    (ObjectProperty.hom_ext _ (Sigma.ι_comp_desc (fun i => (V i).hom.hom) i))
  let J := BigFppfOver.topology B S hS
  let H := Sheaf.sheafifiedYoneda J
  have (i : I) : Mono (f i) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstance : Mono (Sigma.ι W i))
  have hcov : Sieve.ofArrows V f ∈ J U := by
    rw [B.topology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply B.generate_mem_topology_of_isFppfCovering
      (⟨I, fun i => (V i).left, fun i => (f i).left⟩ : PreZeroHypercover U.left)
    simp only [IsFppfCovering, Precoverage.mem_comap_iff,
      PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
    change Presieve.ofArrows W (fun i => Sigma.ι W i) ∈ Scheme.fppfPrecoverage (∐ W)
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (sigmaOpenCover W).mem₀
  have hdisj : ∀ i j, i ≠ j → ∀ (Z : BigFppfOver B S hS)
      (a : Z ⟶ V i) (b : Z ⟶ V j), a ≫ f i = b ≫ f j → ⊥ ∈ J Z := by
    intro i j hij Z a b hab
    have : IsEmpty ((BigFppfOver.toScheme B S hS).obj Z) := ⟨fun z => by
      have hz : (Sigma.ι W i) (a.left.hom z) = (Sigma.ι W j) (b.left.hom z) :=
        congrArg (fun h => ((BigFppfOver.toScheme B S hS).map h) z) hab
      exact hij (congrArg Sigma.fst ((sigmaι_eq_iff W i j _ _).mp hz))⟩
    exact empty_mem_bigFppfOver B S hS Z
  exact ⟨U, H.obj U, ⟨(representedSheafIso B S hS U).symm⟩,
    ⟨(isColimit_represented_disjoint_cover J V U f hcov hdisj).coconePointUniqueUpToIso
      (coproductIsCoproduct fun i => H.obj (V i))⟩⟩

end AlgebraicGeometry.FormalSpace

end
