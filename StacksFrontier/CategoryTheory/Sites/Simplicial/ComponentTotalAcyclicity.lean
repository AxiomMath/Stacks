module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentKInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Components of an injective module on a ringed simplicial site are totally acyclic

Let `S` be a simplicial-site situation and let `O` be a sheaf of rings on its total site. If `I`
is an injective sheaf of `O`-modules, then the abelian sheaf underlying the restriction `I_n` of
`I` to the degree-`n` component is totally acyclic in the sense of Stacks 072Y: its cohomology
over every sheaf of sets on `C_n` vanishes in every positive degree. The sites, the structure
sheaf, the module sections and the `Ext`-groups all sit at the universe of the situation.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekAdjunctionAb`: the adjunction
  `g_{n!} ⊣ g_n^*` between abelian sheaves on a simplicial component and on the total site.
* `CategoryTheory.SimplicialSiteSituation.freeAbelianComponentLowerShriekIso`: lower shriek
  carries the free abelian sheaf on a sheaf of sets to the free abelian sheaf on its image.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isTotallyAcyclic_component_of_injective`:
  **Stacks 0D73**.
* `CategoryTheory.SimplicialSiteSituation.isTotallyAcyclic_componentModule_of_injective`: the
  same conclusion read on the restricted sheaf of modules.

## References

* [Stacks Project, Tag 0D73](https://stacks.math.columbia.edu/tag/0D73)
* [Stacks Project, Tag 072Y](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D6Y](https://stacks.math.columbia.edu/tag/0D6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Stacks.Cohomology

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- The adjunction `g_{n!} ⊣ g_n^*` between abelian sheaves on the degree-`n` simplicial
component and abelian sheaves on the total site. -/
def componentLowerShriekAdjunctionAb :
    sheafPullbackConstruction.sheafPullback (componentFunctor S n) AddCommGrpCat.{u}
        (S.componentTopology n) S.totalTopology ⊣
      S.restrictAb n :=
  sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) AddCommGrpCat.{u}
    (S.componentTopology n) S.totalTopology

/-- Lower shriek from a simplicial component commutes with the free abelian sheaf functor: for a
sheaf of sets `K` on the degree-`n` component, `g_{n!}ℤ_K^♯ ≅ ℤ^♯_{g^{Sh}_{n!}K}`, naturally in
`K`. -/
def freeAbelianComponentLowerShriekIso :
    Sheaf.composeAndSheafify (S.componentTopology n) AddCommGrpCat.free ⋙
        sheafPullbackConstruction.sheafPullback (componentFunctor S n) AddCommGrpCat.{u}
          (S.componentTopology n) S.totalTopology ≅
      sheafPullbackConstruction.sheafPullback (componentFunctor S n) (Type u)
          (S.componentTopology n) S.totalTopology ⋙
        Sheaf.composeAndSheafify S.totalTopology AddCommGrpCat.free :=
  Adjunction.leftAdjointUniq
    ((Sheaf.adjunction (S.componentTopology n) AddCommGrpCat.adj).comp
      (S.componentLowerShriekAdjunctionAb n))
    ((sheafPullbackConstruction.sheafAdjunctionContinuous (componentFunctor S n) (Type u)
        (S.componentTopology n) S.totalTopology).comp
      (Sheaf.adjunction S.totalTopology AddCommGrpCat.adj))

/-- **Stacks Project, Tag 0D73.** Let `O` be a sheaf of rings on the total site of a
simplicial-site situation and let `I` be an injective sheaf of `O`-modules. The abelian sheaf
underlying the restriction `I_n` of `I` to the degree-`n` simplicial component is totally
acyclic: its cohomology over every sheaf of sets on `C_n` vanishes in every positive degree. -/
@[stacks 0D73]
theorem isTotallyAcyclic_component_of_injective
    [HasExt.{u} (Sheaf (S.componentTopology n) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf S.totalTopology AddCommGrpCat.{u})]
    (O : Sheaf S.totalTopology RingCat.{u}) (I : SheafOfModules.{u} O) [Injective I] :
    IsTotallyAcyclic.{u} (S.componentTopology n)
      ((S.restrictAb n).obj ((SheafOfModules.toSheaf O).obj I)) := by
  have : (sheafPullbackConstruction.sheafPullback (componentFunctor S n) AddCommGrpCat.{u}
      (S.componentTopology n) S.totalTopology).Additive :=
    (S.componentLowerShriekAdjunctionAb n).left_adjoint_additive
  have hex := (exactFunctor_iff _).1 (componentLowerShriek_exactFunctor S n)
  have : PreservesFiniteLimits (sheafPullbackConstruction.sheafPullback (componentFunctor S n)
    AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology) := hex.1
  have : PreservesFiniteColimits (sheafPullbackConstruction.sheafPullback (componentFunctor S n)
    AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology) := hex.2
  intro K p hp
  have htotal := isTotallyAcyclic_of_injective S.totalTopology O I
    ((sheafPullbackConstruction.sheafPullback (componentFunctor S n) (Type u)
      (S.componentTopology n) S.totalTopology).obj K) p hp
  have hzero : Subsingleton (Abelian.Ext.{u}
      ((sheafPullbackConstruction.sheafPullback (componentFunctor S n) AddCommGrpCat.{u}
          (S.componentTopology n) S.totalTopology).obj
        ((Presheaf.freeAbelianSheaf (S.componentTopology n)).obj K.obj))
      ((SheafOfModules.toSheaf O).obj I) p) :=
    (((Abelian.extFunctor p).mapIso ((S.freeAbelianComponentLowerShriekIso n).app K).op).app
      ((SheafOfModules.toSheaf O).obj I)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp htotal
  exact ⟨fun x y =>
    (Stacks.ExtAdjunction.extMap_bijective (S.componentLowerShriekAdjunctionAb n) _ _ p).1
      (@Subsingleton.elim _ hzero _ _)⟩

/-- **Stacks Project, Tag 0D73**, with the conclusion read on the restricted sheaf of modules.
The restriction of an injective sheaf of `O`-modules to the degree-`n` simplicial component —
reindexing the sections and restricting the scalars along the identity of the restricted sheaf
of rings — has totally acyclic underlying abelian sheaf. -/
@[stacks 0D73 "the conclusion read on the restricted sheaf of modules rather than on the
  restriction of the underlying abelian sheaf"]
theorem isTotallyAcyclic_componentModule_of_injective
    [HasExt.{u} (Sheaf (S.componentTopology n) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf S.totalTopology AddCommGrpCat.{u})]
    (O : Sheaf S.totalTopology RingCat.{u}) (I : SheafOfModules.{u} O) [Injective I] :
    IsTotallyAcyclic.{u} (S.componentTopology n)
      ((SheafOfModules.toSheaf _).obj
        ((SheafOfModules.pushforward (F := componentFunctor S n)
          (𝟙 (((componentFunctor S n).sheafPushforwardContinuous RingCat.{u}
            (S.componentTopology n) S.totalTopology).obj O))).obj I)) :=
  S.isTotallyAcyclic_component_of_injective n O I

end CategoryTheory.SimplicialSiteSituation

end
