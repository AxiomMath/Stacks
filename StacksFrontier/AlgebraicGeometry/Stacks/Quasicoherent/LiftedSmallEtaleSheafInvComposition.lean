module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition

/-!
# The composition law for the inverse identification of factors 2, 3 and 4 of Stacks 076T

`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is factors 2, 3 and 4 of the identification
of sections of `AlgebraicGeometry.Stack.liftedSectionsIso`, read backwards as a morphism of
*sheaves* of modules.  This file gives it a composition law: for arrows `ψ : z' ⟶ z` and
`φ : z ⟶ x` of `𝒳`, the identification at `ψ` whose input is the identification at `φ` is the
base change of the composition law for the pullbacks of modules on the schemes below, followed
by the identification at `φ ∘ ψ`.

That law is what factors 2, 3 and 4 have none of in the shape they are built in — a
sheafification unit, a sheafified comparison and the base change of **Stacks 03LC (1)** — and
it is the one step of the proof of **Stacks 076T** that
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleAssembly.lean` carries
as `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn`, up to reading it on sections
over the final object of the small étale site.

## The proof

Three inputs, and pure category algebra between them:

1. **Stacks 075D (1)** for the third factor.  The composition law of the adjunct of `c_φ` is
   `AlgebraicGeometry.Stack.sheafifiedRestrictModulePullbackComparison_comp`; this file first
   restates it at the name `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, which the
   composition law consumes.  Only the spelling differs — the two statements are definitionally
   the same, and the proof is `exact`.
2. the pentagon `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp` of
   **Stacks 03LC (1)** for the first factor;
3. the naturality in the module of
   `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` for the middle factor.

## Implementation notes

The algebra is factored out as a lemma with every object and arrow abstract.  A sheafified
Stacks 06WC pullback has two definitionally equal spellings — the functor
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, and a sheafification of a pullback of
presheaves of modules, which is the spelling
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` states its source in — and
the chain changes spelling from one junction to the next, so `rw` matches `Category.assoc` and
`CategoryTheory.Functor.map_comp` at none of them even where the pattern is plainly there.  With
the objects abstract the algebra is `rw`-able, and the application is one `exact`.

## Main results

* `AlgebraicGeometry.Stack.sheafifiedRestrictComparison_comp`: **Stacks 075D (1) for the named
  adjunct of `c_φ`.**
* `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp`: **the composition law for
  `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`.**

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **Stacks 075D (1) for the named adjunct of the comparison map `c_φ` of Stacks 06WC.**  For
arrows `ψ : z' ⟶ z` and `φ : z ⟶ x` of `𝒳` and a presheaf of modules `F` whose small étale
restrictions at the three objects are sheaves, the sheafified Stacks 06WC pullback along `ψ` of
the adjunct below `φ`, followed by the adjunct below `ψ`, is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` followed by the adjunct below
`ψ ∘ φ`.

This is `AlgebraicGeometry.Stack.sheafifiedRestrictModulePullbackComparison_comp` with each
adjunct read at the name `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, which is the
factor of `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` the composition law for that map
consumes.  No hypothesis on the arrows is used; in particular neither comparison map is assumed
invertible. -/
theorem sheafifiedRestrictComparison_comp {x z z' : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf) :
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ).map
          (sheafifiedRestrictComparison B E h S hS p hp F φ hMz) ≫
        sheafifiedRestrictComparison B E h S hS p hp F ψ hMz' =
      (sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ φ).hom.app
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) F x hMx) ≫
        sheafifiedRestrictComparison B E h S hS p hp F (ψ ≫ φ) hMz' :=
  sheafifiedRestrictModulePullbackComparison_comp B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F ψ φ hMz' hMz hMx

/-- The pure category algebra of the composition law for
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, with every object and arrow abstract.

Read `a'`, `g`, `w` as the three factors of the identification at `ψ` whose input is the
identification at `φ`, with `g` the sheafified Stacks 06WC pullback along `ψ` of the latter,
split by `hg` and `hgg` into its own three factors `f'`, `u`, `v`; and read
`m ≫ b' ≫ q ≫ c` as the base change of the composition law for the pullbacks of modules on the
schemes followed by the identification at `φ ∘ ψ`.  The three squares consumed are the pentagon
`hpent` of **Stacks 03LC (1)**, the naturality `hnat` of the comparison of the two sheafified
pullbacks and **Stacks 075D (1)** as `h075`; the remaining four hypotheses are inverse laws.

Stating the algebra abstractly is not decoration.  A sheafified Stacks 06WC pullback has two
spellings — the functor `AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, and a
sheafification of a pullback of presheaves of modules, which is what
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` states its source as.  They
are definitionally equal, so every composite below elaborates, but the middle object of a
composite is *recorded* in one spelling at one junction of the chain and in the other at the
next, and `rw` matches at neither.  With the objects abstract the algebra is `rw`-able, and the
application is a single `exact`, which unifies up to definitional equality. -/
private theorem sheafInv_comp_algebra {C : Type*} [Category C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : C}
    {a' : O₁ ⟶ O₂} {a : O₂ ⟶ O₁} {f' : O₂ ⟶ O₃} {f : O₃ ⟶ O₂}
    {u : O₃ ⟶ O₄} {v : O₄ ⟶ O₅} {w : O₅ ⟶ O₆} {g : O₂ ⟶ O₅} {gg : O₃ ⟶ O₅}
    {k : O₃ ⟶ O₇} {k' : O₄ ⟶ O₈} {q : O₇ ⟶ O₈} {c : O₈ ⟶ O₆}
    {m : O₁ ⟶ O₉} {n : O₉ ⟶ O₁} {b : O₇ ⟶ O₉} {b' : O₉ ⟶ O₇}
    (hg : g = f' ≫ gg) (hgg : gg = u ≫ v)
    (hpent : f ≫ a = k ≫ b ≫ n) (hnat : u ≫ k' = k ≫ q) (h075 : v ≫ w = k' ≫ c)
    (hn : n ≫ m = 𝟙 O₉) (hf : f' ≫ f = 𝟙 O₂) (ha : a' ≫ a = 𝟙 O₁) (hb : b ≫ b' = 𝟙 O₇) :
    a' ≫ g ≫ w = m ≫ b' ≫ q ≫ c := by
  have hk : f ≫ a ≫ m ≫ b' = k := by
    rw [← Category.assoc f, hpent]
    simp only [Category.assoc]
    rw [← Category.assoc n m b', hn, Category.id_comp, hb, Category.comp_id]
  subst hgg
  subst hg
  rw [Category.assoc, Category.assoc, h075, ← Category.assoc u, hnat, Category.assoc, ← hk]
  simp only [Category.assoc]
  rw [← Category.assoc f' f, hf, Category.id_comp, ← Category.assoc a' a, ha, Category.id_comp]

/-- The morphism of schemes below a composable pair of arrows of `𝒳`: the morphism below `ψ`
followed by the morphism below `φ` is the morphism below `φ ∘ ψ`.

This is the factorisation `AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp` is read at in
the composition law for `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`. -/
theorem belowSchemeHom_comp {x z z' : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) :
    B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left =
      B.inclusion.map (p.map (ψ ≫ φ)).left := by
  rw [p.map_comp]
  exact (B.inclusion.map_comp _ _).symm

/-- **The composition law for `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`.**  For arrows
`ψ : z' ⟶ z` and `φ : z ⟶ x` of `𝒳`, a module `𝓕` below `x` and a morphism of sheaves of modules
`e : 𝓕^a ⟶ F|_{U_ét}`, the inverse identification at `ψ` *whose input is the inverse
identification at `φ`* is the base change of the composition law
`AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp` for the pullbacks of modules on the
schemes below, followed by the inverse identification at `φ ∘ ψ` with the same input `e`.

This is the composition law factors 2, 3 and 4 of the identification of sections of
`AlgebraicGeometry.Stack.liftedSectionsIso` have none of in the shape they are built in; it is
available here because `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is a morphism of
*sheaves* of modules, where both of the laws of the two factors that have one live — the
pentagon `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp` of
**Stacks 03LC (1)** and `AlgebraicGeometry.Stack.sheafifiedRestrictComparison_comp`, which is
**Stacks 075D (1)** for the adjunct of `c_φ`.  The middle factor contributes the naturality of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` in the module, and nothing else is
used: in particular neither comparison map of **Stacks 06WC** is assumed invertible, and `𝓕` is
not assumed quasi-coherent. -/
theorem liftedSmallEtaleSheafInv_comp {x z z' : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx) :
    liftedSmallEtaleSheafInv B E h S hS p hp F ψ
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) hMz hMz'
          (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e) =
      (SmallEtale.associatedModule E (p.obj z').left.1 (contains_base B E h S hS p z')).map
          ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
            (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
            (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕) ≫
        liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz' e :=
  sheafInv_comp_algebra
    ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ).map_comp
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ 𝓕).inv
      ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).map e ≫
        sheafifiedRestrictComparison B E h S hS p hp F φ hMz))
    ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ).map_comp
      ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).map e)
      (sheafifiedRestrictComparison B E h S hS p hp F φ hMz))
    (associatedModuleObjSmallEtaleBaseChangeIso_comp B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ φ 𝓕)
    ((sheafifiedPullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ φ).hom.naturality e)
    (sheafifiedRestrictComparison_comp B E h S hS p hp F ψ φ hMx hMz hMz')
    ((SmallEtale.associatedModule E (p.obj z').left.1
        (contains_base B E h S hS p z')).mapIso
      ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
        (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
        (belowSchemeHom_comp B S hS p ψ φ)).app 𝓕)).inv_hom_id
    ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ).mapIso
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ 𝓕)).inv_hom_id
    (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).inv_hom_id
    (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (ψ ≫ φ) 𝓕).hom_inv_id


end AlgebraicGeometry.Stack

end
