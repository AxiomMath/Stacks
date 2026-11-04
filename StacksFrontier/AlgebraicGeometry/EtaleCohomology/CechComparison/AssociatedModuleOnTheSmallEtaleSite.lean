module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnCoarserTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated module of a quasi-coherent sheaf on the small étale site

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module. On the small étale site
`AlgebraicGeometry.Scheme.Etale` of `S`, the presheaf `Fᵃ : T ↦ Γ(T, f⁺ F)` of
[Stacks, Tag 03OG] is a sheaf of modules over the structure sheaf `𝒪`, the sheaf of global
functions. Its cohomology is the right-hand side of [Stacks, Tag 03P2] in the case
`𝒞 = S_étale`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleStructureSheaf`: the structure sheaf `𝒪` of the small
  étale site of `S`.
* `Stacks.EtaleCohomology.smallEtaleAssociatedModule`: the sheaf of `𝒪`-modules `Fᵃ` on the
  small étale site of `S`.

## Main results

* `CategoryTheory.Functor.isContinuous_of_le`: continuity of a functor of sites is preserved
  when the topology on the target is replaced by a coarser one.
* `AlgebraicGeometry.Scheme.Etale.forget_isContinuous_fpqcOver`: the forgetful functor from the
  small étale site of `S` to the schemes over `S` is continuous for the localized fpqc
  topology.
* `Stacks.EtaleCohomology.isSheaf_smallEtaleAssociatedPresheaf`: the presheaf underlying `Fᵃ`
  satisfies the sheaf condition on the small étale site.

## References

* [Stacks Project, Tag 03OG](https://stacks.math.columbia.edu/tag/03OG)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

/-- Continuity of a functor of sites is preserved when the topology on the target is replaced
by a coarser one. -/
public theorem isContinuous_of_le {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) (J : GrothendieckTopology C)
    {K K' : GrothendieckTopology D} [F.IsContinuous J K'] (hK : K' ≤ K) :
    F.IsContinuous J K :=
  ⟨fun G ↦ Functor.IsContinuous.op_comp_isSheaf_of_types (F := F) (J := J) (K := K')
    ⟨G.obj, Presheaf.IsSheaf.of_le hK G.2⟩⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The forgetful functor from the small étale site of `S` to the schemes over `S` is
continuous for the localized fpqc topology. -/
public instance Scheme.Etale.forget_isContinuous_fpqcOver (S : Scheme.{u}) :
    (Scheme.Etale.forget S).IsContinuous (Scheme.smallEtaleTopology S)
      (Scheme.fpqcTopology.{u}.over S) :=
  letI := Scheme.Etale.forget_isContinuous S
  CategoryTheory.Functor.isContinuous_of_le _ _
    (Stacks.Sites.over_mono Stacks.Sites.etaleTopology_le_fpqcTopology S)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

/-- The functor reading an object of the small étale site of `S` as a scheme over `S`. -/
public abbrev smallEtaleToOver : S.Etale ⥤ CategoryTheory.Over S :=
  AlgebraicGeometry.Scheme.Etale.forget S

/-- Global functions are a sheaf of rings on the small étale site of `S`. -/
public theorem isSheaf_smallEtaleStructurePresheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology S)
      (Stacks.Sites.structurePresheaf S (smallEtaleToOver S)) :=
  isSheaf_structurePresheaf_of_isContinuous S (smallEtaleToOver S)
    (Scheme.smallEtaleTopology S)

/-- The presheaf `Fᵃ : T ↦ Γ(T, f⁺ F)` of [Stacks, Tag 03OG] satisfies the sheaf condition on
the small étale site of `S`. -/
public theorem isSheaf_smallEtaleAssociatedPresheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology S)
      (Stacks.Sites.associatedPresheaf S F (smallEtaleToOver S)) :=
  isSheaf_associatedPresheaf_of_isContinuous S F (smallEtaleToOver S)
    (Scheme.smallEtaleTopology S)

/-- The structure sheaf `𝒪` of the small étale site of `S`: its sections over an object are
the global functions on the underlying scheme. -/
@[sga "4 VII 2.1" "special case"]
public noncomputable def smallEtaleStructureSheaf :
    Sheaf (Scheme.smallEtaleTopology S) RingCat.{u} :=
  structureSheafOfIsContinuous S (smallEtaleToOver S) (Scheme.smallEtaleTopology S)

/-- The associated module `Fᵃ` of a quasi-coherent module `F` on `S`, as a sheaf of
`𝒪`-modules on the small étale site of `S`. Its sections over an object `T` are the global
sections of the pullback of `F` to the scheme underlying `T`. -/
public noncomputable def smallEtaleAssociatedModule :
    SheafOfModules.{u} (smallEtaleStructureSheaf S) :=
  associatedModuleOfIsContinuous S F (smallEtaleToOver S) (Scheme.smallEtaleTopology S)

/-- The underlying abelian presheaf of `Fᵃ` on the small étale site is the restriction along
the forgetful functor of the presheaf of pullback sections of [Stacks, Tag 03DS]. -/
@[simp]
public theorem smallEtaleAssociatedModule_presheaf :
    (smallEtaleAssociatedModule S F).val.presheaf =
      Stacks.Sites.associatedPresheaf S F (smallEtaleToOver S) := rfl

end Stacks.EtaleCohomology
