module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverZariskiPrecoverage

/-!
# A Zariski family of the big h category over `S` and the family of its images

A Zariski family `f i : X i ⟶ U` of the big h category over `S` is a jointly surjective family of
open immersions. Each member is isomorphic, over `U`, to the inclusion of its image
`(f i).opensRange`, an open of the underlying scheme of `U` which is again an object of the site
(`AlgebraicGeometry.BigHOver.opensObj`). So the family and the family of inclusions of the images
generate the same sieve, and the stack condition for a pseudofunctor at the family is the stack
condition at the family of images.

This is what lets a Zariski descent argument be run for families of *opens* only. Two points make
the reduction worth stating once. The families of the site are indexed by arbitrary types, in
particular by types of `Type (u + 1)`, while the family of images is indexed by a set of opens, a
type of `Type u`; and its members are the inclusions `AlgebraicGeometry.BigHOver.opensι`, the
shape in which the gluing of sheaves along opens is available.

## Main results

* `AlgebraicGeometry.BigHOver.isStackFor_of_isStackFor_opens`: **a pseudofunctor on the big h
  category over `S` is a stack for a Zariski family as soon as it is a stack for every family of
  opens covering the base.**

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe t u v' u'

namespace AlgebraicGeometry.BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The isomorphism of a member of the big h category over `S` mapping by an open immersion to
`U` onto its image, as a morphism of the site into the open of the image. -/
noncomputable def toOpensRange {X U : BigHOver B S hS} (f : X ⟶ U)
    [IsOpenImmersion ((toScheme B S hS).map f)] :
    X ⟶ opensObj B S hS ((toScheme B S hS).map f).opensRange :=
  Over.homMk (ObjectProperty.homMk ((toScheme B S hS).map f).isoOpensRange.hom) (by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, opensObj_hom_hom, ← Category.assoc]
    change (((toScheme B S hS).map f).isoOpensRange.hom ≫ _) ≫ U.hom.hom = X.hom.hom
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact congrArg (fun k => k.hom) (Over.w f))

/-- The inverse of `AlgebraicGeometry.BigHOver.toOpensRange`, as a morphism of the site. -/
noncomputable def ofOpensRange {X U : BigHOver B S hS} (f : X ⟶ U)
    [IsOpenImmersion ((toScheme B S hS).map f)] :
    opensObj B S hS ((toScheme B S hS).map f).opensRange ⟶ X :=
  Over.homMk (ObjectProperty.homMk ((toScheme B S hS).map f).isoOpensRange.inv) (by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, opensObj_hom_hom]
    change _ = ((toScheme B S hS).map f).opensRange.ι ≫ U.hom.hom
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    exact congrArg (fun k => ((toScheme B S hS).map f).isoOpensRange.inv ≫ k.hom) (Over.w f).symm)

/-- A member mapping by an open immersion factors through the inclusion of its image. -/
@[reassoc (attr := simp)]
theorem toOpensRange_opensι {X U : BigHOver B S hS} (f : X ⟶ U)
    [IsOpenImmersion ((toScheme B S hS).map f)] :
    toOpensRange f ≫ opensι B S hS ((toScheme B S hS).map f).opensRange = f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom]
  exact Scheme.Hom.isoOpensRange_hom_ι _

/-- The inclusion of the image of a member mapping by an open immersion factors through the
member. -/
@[reassoc (attr := simp)]
theorem ofOpensRange_comp {X U : BigHOver B S hS} (f : X ⟶ U)
    [IsOpenImmersion ((toScheme B S hS).map f)] :
    ofOpensRange f ≫ f = opensι B S hS ((toScheme B S hS).map f).opensRange := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom]
  exact Scheme.Hom.isoOpensRange_inv_comp _

/-- **A pseudofunctor on the big h category over `S` is a stack for a Zariski family as soon as it
is a stack for every family of opens of the base covering it.**

The family of opens used is the set of images of the members, indexed by a type of `Type u`; the
family and the inclusions of its images generate the same sieve, each member being isomorphic over
the base to the inclusion of its image. -/
theorem isStackFor_of_isStackFor_opens
    (F : Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{v', u'})
    {U : BigHOver B S hS} {ι : Type t} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U)
    (h : ∀ {T : Type u} (W : T → ((toScheme B S hS).obj U).Opens), ⨆ k, W k = ⊤ →
      F.IsStackFor (Presieve.ofArrows (fun k => opensObj B S hS (W k))
        (fun k => opensι B S hS (W k)))) :
    F.IsStackFor (Presieve.ofArrows X f) := by
  rw [BigHOver.zariskiPrecoverage_eq_comap, Precoverage.mem_comap_iff,
    Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at hf
  have : ∀ i, IsOpenImmersion ((toScheme B S hS).map (f i)) := hf.2
  let T := {V : ((toScheme B S hS).obj U).Opens //
    ∃ i, V = ((toScheme B S hS).map (f i)).opensRange}
  let W : T → ((toScheme B S hS).obj U).Opens := Subtype.val
  have hW : ⨆ k, W k = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, y, rfl⟩ := hf.1 x
    exact Opens.mem_iSup.2 ⟨⟨_, i, rfl⟩, ⟨y, rfl⟩⟩
  refine (F.isStackFor_iff_of_sieve_eq (le_antisymm ?_ ?_)).mpr (h W hW)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨_, toOpensRange (f i), opensι B S hS ((toScheme B S hS).map (f i)).opensRange,
      Presieve.ofArrows.mk (⟨_, i, rfl⟩ : T), toOpensRange_opensι (f i)⟩
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟨V, i, rfl⟩⟩
    exact ⟨_, ofOpensRange (f i), f i, Presieve.ofArrows.mk i, ofOpensRange_comp (f i)⟩

end AlgebraicGeometry.BigHOver

end
