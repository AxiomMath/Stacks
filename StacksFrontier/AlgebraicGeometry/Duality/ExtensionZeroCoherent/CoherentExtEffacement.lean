module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.EpiEffacement
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapBijectiveBounded
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules

/-!
# Effacing an `Ext`-class of any positive degree between coherent modules, coherently

Let `X` be a Noetherian scheme and let `F`, `G` be coherent `𝒪_X`-modules. Every class in
`Ext^{n + 1}_X(F, G)` dies after restriction along an epimorphism `E ⟶ F` **whose source is
again coherent**.

This is the input the dévissage of [Stacks, Tag 0G2H] runs on, and the reason the source of that
tag invokes `D^b_{Coh}(𝒪_X) = D^b(Coh(𝒪_X))`: the effacing epimorphism `α : E ⟶ F` is fed to
Artin--Rees and to the inductive hypothesis of the induction on the degree, both of which need
`E` and `ker α` coherent. `Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero` does
this in degree one without any derived-category input, because there `Ext^1` *is* the group of
extensions; in degrees `≥ 2` a Yoneda extension in `Mod(𝒪_X)` representing the class has middle
terms with no reason to be coherent, and the way to coherent middle terms is to compute the
`Ext`-group in the abelian category `Coh(𝒪_X)` instead.

## The two inputs

* `CategoryTheory.Functor.bijective_mapExtAddHom_of_boundedFullyFaithful`: `Ext`-groups are
  computed in a subcategory whose bounded derived category embeds fully faithfully. Its
  hypothesis here is the fully faithfulness half of [Stacks, Tag 0FDB],
  `AlgebraicGeometry.full_boundedι_comp_coherentInModulesι` and
  `AlgebraicGeometry.faithful_boundedι_comp_coherentInModulesι`.
* `CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero`: in any abelian category a class of
  positive degree is effaced by an epimorphism of its source. Applied to `Coh(𝒪_X)` — which has
  no injectives, so the injective-resolution effacement does not apply — it produces an
  epimorphism *of coherent modules*.

Pushing that epimorphism forward along the exact inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` keeps it an
epimorphism and keeps the class it kills, because `Ext.mapExactFunctor` commutes with `mk₀` and
with Yoneda composition.

## Main results

* `Stacks.ExtEffacement.bijective_mapExtAddHom_coherentInModules`: **[Stacks, Tag 0FDB] read on
  `Ext`-groups** — for coherent `F`, `G` on a Noetherian scheme the canonical map
  `Ext^n_{Coh(𝒪_X)}(F, G) ⟶ Ext^n_{Mod(𝒪_X)}(F, G)` is bijective.
* `Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos_sheafOfModules`: **a
  positive-degree `Ext`-class between coherent modules is effaced by an epimorphism from a
  coherent module**, and
  `Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos`, the same statement in
  the `AlgebraicGeometry.Scheme.Modules` spelling the consumers use.

## Implementation notes

`Mod(𝒪_X)` is spelled `SheafOfModules X.ringCatSheaf` in the two statements above, rather than
the definitionally equal `AlgebraicGeometry.Scheme.Modules X`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/DerivedCoherent/Modules.lean`: that is the spelling
[Stacks, Tag 0FDB] is stated at, and `Scheme.Modules` is a `def` carrying its own `Category`
instance, through which neither the `Abelian` instance of the coherent full subcategory nor the
fully faithfulness instances of [Stacks, Tag 0FDB] are found. The `Scheme.Modules` form of the
effacement is deduced from the other by the identity, the two `Category` instances having the
same fields; nothing has to be transported.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance of raised
priority, as in the file proving [Stacks, Tag 0FDB]: that is the model its fully faithfulness
instances are stated at, and the import closure carries locally small models at universe `u` as
global instances too.

## References

* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 06XU](https://stacks.math.columbia.edu/tag/06XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w w' u

namespace Stacks.ExtEffacement

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 0FDB] read on `Ext`-groups.** On a Noetherian scheme the canonical map
`Ext^n_{Coh(𝒪_X)}(F, G) ⟶ Ext^n_{Mod(𝒪_X)}(F, G)` between coherent modules is bijective: the
`Ext`-groups of coherent modules may be computed in the abelian category of coherent modules.

The functor `D^b(Coh(𝒪_X)) ⥤ D(𝒪_X)` is fully faithful, which is what
`CategoryTheory.Functor.bijective_mapExtAddHom_of_boundedFullyFaithful` consumes. -/
public theorem bijective_mapExtAddHom_coherentInModules [IsNoetherian X]
    [HasExt.{w'} (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)]
    [HasExt.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Function.Bijective ((coherentInModules X).ι.mapExtAddHom F G n) :=
  (coherentInModules X).ι.bijective_mapExtAddHom_of_boundedFullyFaithful F G n

/-- **A positive-degree `Ext`-class between coherent modules is effaced by an epimorphism from a
coherent module.** For `ξ ∈ Ext^{n + 1}_X(F, G)` with `F`, `G` coherent on a Noetherian scheme
there is an epimorphism `p : E ⟶ F` with `E` coherent and `ξ ∘ p = 0`.

The class is pulled back to `Ext^{n + 1}_{Coh(𝒪_X)}(F, G)` along the bijection of
`Stacks.ExtEffacement.bijective_mapExtAddHom_coherentInModules`, effaced there by
`CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero` — which needs nothing of `Coh(𝒪_X)` beyond
its being abelian — and the effacing epimorphism is pushed back to `Mod(𝒪_X)`, where it is still
an epimorphism because the inclusion is exact.

This is the general-degree form of
`Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero`, which is the case `n = 0` proved
without any derived-category input. -/
public theorem exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos_sheafOfModules [IsNoetherian X]
    [HasExt.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    {F G : SheafOfModules.{u} X.ringCatSheaf} [hF : F.IsCoherent] [hG : G.IsCoherent] {n : ℕ}
    (ξ : Ext.{w} F G (n + 1)) :
    ∃ (E : SheafOfModules.{u} X.ringCatSheaf) (p : E ⟶ F), E.IsCoherent ∧ Epi p ∧
      (Ext.mk₀ p).comp ξ (zero_add (n + 1)) = 0 := by
  let := HasExt.standard (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  let : ((coherentInModules X).ι).PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _
  obtain ⟨η, hη⟩ :=
    (bijective_mapExtAddHom_coherentInModules ⟨F, hF⟩ ⟨G, hG⟩ (n + 1)).surjective ξ
  obtain ⟨E, p, hp, hzero⟩ := CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero n η
  have := hp
  refine ⟨E.obj, (coherentInModules X).ι.map p, E.property, inferInstance, ?_⟩
  have h := congrArg (fun z => Ext.mapExactFunctor (coherentInModules X).ι z) hzero
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_zero] at h
  have hη' : Ext.mapExactFunctor (coherentInModules X).ι η = ξ := hη
  rw [← hη']
  exact h

/-- **A positive-degree `Ext`-class between coherent modules is effaced by an epimorphism from a
coherent module**, in the `AlgebraicGeometry.Scheme.Modules` spelling of `Mod(𝒪_X)` that the
consumers of this statement use — among them the degree-one sibling
`Stacks.ExtEffacement.exists_isCoherent_epi_mk₀_comp_eq_zero` and the `Ext`-groups of
`Stacks.AlgebraicGeometry.IdealPowerColimit`.

`AlgebraicGeometry.Scheme.Modules X` is `SheafOfModules X.ringCatSheaf` by `rfl`, and its
`Category` instance has the same fields, so the two `HasExt` assertions and the two `Ext`-groups
are definitionally the same and the transport is the identity. -/
public theorem exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos [IsNoetherian X]
    [HasExt.{w} X.Modules] {F G : X.Modules} [F.IsCoherent] [G.IsCoherent] {n : ℕ}
    (ξ : Ext.{w} F G (n + 1)) :
    ∃ (E : X.Modules) (p : E ⟶ F), E.IsCoherent ∧ Epi p ∧
      (Ext.mk₀ p).comp ξ (zero_add (n + 1)) = 0 := by
  let : HasExt.{w} (SheafOfModules.{u} X.ringCatSheaf) := ‹HasExt.{w} X.Modules›
  exact exists_isCoherent_epi_mk₀_comp_eq_zero_of_pos_sheafOfModules (X := X) (F := F) (G := G) ξ

end Stacks.ExtEffacement

end
