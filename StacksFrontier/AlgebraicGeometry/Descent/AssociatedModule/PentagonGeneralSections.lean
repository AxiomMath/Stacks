module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSectionsCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PentagonAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PseudonaturalAssembly

/-!
# The pentagon of Stacks 03DV, assembled: the comparison of sections and its cocycle

`AlgebraicGeometry.BigFppfOver.NatIsoCompSquare` is the one coherence on which Stacks 03DX (1)
still rests in this library: the comparison

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`

of Stacks 03DV is compatible with composition of objects of the big fppf site.  Both of the
functors it compares are left adjoints, so the square is equivalent to the pentagon between the
mates of its four factors, and
`Stacks.Mates.trans_assoc_of_conjugate_of_mates` states that pentagon with the four mates already
replaced by the isomorphisms they have been computed to be.

This file performs that replacement.  The point is *which* adjunction for restriction to an object
is used.  With `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` the mate of
`AlgebraicGeometry.BigFppfOver.objRestrictComp` carries three occurrences of
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` — the comparison of the two right
adjoints of restriction, which nothing in the pentagon cancels, and two of which occur whiskered,
where replacing them by their closed form re-spells the whiskered functor and exceeds
the heartbeat budget.  With
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` instead, that mate is
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp`, which has no such occurrence at
all, and the three comparisons of right adjoints are absorbed once and for all into the three
mates of Stacks 03DV itself.

What is left is a cocycle condition for one isomorphism of functors,
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso`:

    `𝒢|_{(Sch/X)_fppf}` taken on `X_Zar` and pushed to `S_Zar`
      ≅ `𝒢` base changed to `(Sch/X)_fppf` and taken on `S_Zar`,

an identity between composites of *pushforwards* of sheaves of modules in which neither the
associated-module functor nor any `CategoryTheory.Adjunction.leftAdjointUniq` occurs.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso`: **the comparison of Stacks 03DV read on
  the side of the right adjoints**, that is, its mate with respect to
  `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`.  It compares the two routes
  from a module on the big fppf site of the scheme `X` of `T` to an `𝒪_S`-module: base change
  along the structure morphism of `T` followed by taking sections on the small Zariski site of
  `S`, and taking sections on the small Zariski site of `X` followed by the pushforward along the
  structure morphism.  Every one of those four functors is a pushforward.
* `AlgebraicGeometry.BigFppfOver.SectionsCocycle`: the cocycle condition for that comparison at a
  morphism of the big fppf site, written as a proposition.

## Main results

* `AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_sectionsCocycle`: **the square for
  Stacks 03DV at a morphism follows from the cocycle for the comparison of sections at that
  morphism.**
* `AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural_of_sectionsCocycle`: **the
  comparison of Stacks 03DV is pseudonatural as soon as that cocycle holds at every base** — that
  is, `AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural`, the hypothesis every consumer
  of Stacks 03DX (1) in this library carries, follows from one identity between composites of
  pushforwards.

## Implementation notes

Nothing here carries a `stacks` attribute: Stacks 03DX (1) is still a hypothesis, and a hypothesis
is part of a citation.

**Why the mates of Stacks 03DV are left as mates.**
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` is defined as a
`CategoryTheory.conjugateIsoEquiv` rather than as an explicit composite.  Its value is
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_associatedModuleObjRestrictNatIso` conjugated by
`objRestrictRightAdjointIso`, through `Stacks.Mates.conjugateIsoEquiv_congr_target`,
`AlgebraicGeometry.BigFppfOver.rightAdjointUniq_comp` and
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_refl_objRestrict`; writing that composite into
the definition would put the comparison of right adjoints back into the statement of the cocycle,
which is precisely what choosing this family of adjunctions removes.  The three occurrences of
that comparison are instead confined to the three separate computations of the three
`objRestrictSectionsIso`, where each occurs *unwhiskered at the head* of a `whiskerRight`, which
is the position in which `AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso_eq` is
affordable.

**Why the three mates of Stacks 03DV are discharged by `rfl`.**  The hypotheses `hNT`, `hNU`,
`hNT'` of `Stacks.Mates.trans_assoc_of_conjugate_of_mates` ask for the three mates to be equal to
the three named isomorphisms, and `objRestrictSectionsIso` is defined to be exactly those mates;
no computation is performed by the assembly, and the cost of the whole reduction is the cost of
one application of the generic lemma.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of Stacks 03DV read on the right adjoints -/

/-- **The comparison of Stacks 03DV read on the side of the right adjoints.**  For `T` an object
of the big fppf category over `S` with structure morphism `f : X ⟶ S`, this is the mate of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` with respect to
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, so an isomorphism

    `𝒢 ↦ (𝒢 base changed along f) on S_Zar  ≅  𝒢 ↦ f_*(𝒢 on X_Zar)`

of functors from sheaves of modules on the big fppf site of `X` to `𝒪_S`-modules.

All four functors it is built from are pushforwards of sheaves of modules —
`SheafOfModules.overPullback` along `f` inside the big fppf category,
`AlgebraicGeometry.BigFppfOver.restrictModule` along the inclusion of a small Zariski site, and
`AlgebraicGeometry.Scheme.Modules.pushforward` along `f` — so this is the form of the comparison
in which it is a statement about sections.  Neither the associated-module functor nor the
comparison of the two right adjoints of restriction to an object appears in the *statement*; both
are absorbed into the mate. -/
public noncomputable abbrev objRestrictSectionsIso (T : BigFppfOver B S hS) :=
  conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp
      (objRestrictOverPullbackAdjunction B S hS T))
    ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
      (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (associatedModuleObjRestrictNatIso B S hS T)

/-- **The cocycle condition for the comparison of sections of Stacks 03DV.**  For `g : T' ⟶ T` a
morphism of the big fppf category over `S`, the comparison
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` at `T'` agrees with the two-step route
through `T`: the comparison at `T` whiskered by base change along `g`, the comparison at `g` read
over the scheme of `T` whiskered by the pushforward along the structure morphism of `T`, the
contraction `Stacks.SheafOfModules.overPullbackComp` of the iterated base change, and the
contraction `AlgebraicGeometry.Scheme.Modules.pushforwardComp` of the iterated pushforward of
modules on schemes.

This is the pentagon of `Stacks.Mates.trans_assoc_of_conjugate_of_mates` for the comparison of
Stacks 03DV with the four mates substituted, in the orientation that lemma asks for.  It is the
residue of Stacks 03DX (1) in this library: an identity between composites of pushforwards of
sheaves of modules, containing no associated-module functor, no
`CategoryTheory.Adjunction.leftAdjointUniq` and no comparison of two right adjoints. -/
public abbrev SectionsCocycle {T T' : BigFppfOver B S hS} (g : T' ⟶ T) : Prop :=
  Functor.isoWhiskerLeft
        (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
        (eqToIso (congrArg
              (fun k : objScheme B S hS T' ⟶ S => Scheme.Modules.pushforward k)
              (objHom_comp B S hS g)).symm ≪≫
            (Scheme.Modules.pushforwardComp
              (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
              (objHom B S hS T)).symm).symm ≪≫
      (objRestrictSectionsIso B S hS T').symm =
    (Functor.associator
          (restrictModule B (objScheme B S hS T') (contains_objScheme B S hS T'))
          (Scheme.Modules.pushforward
            (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)))
          (Scheme.Modules.pushforward (objHom B S hS T))).symm ≪≫
      Functor.isoWhiskerRight
          (objRestrictSectionsIso B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)).symm
          (Scheme.Modules.pushforward (objHom B S hS T)) ≪≫
        (Functor.isoWhiskerRight
              (Stacks.SheafOfModules.overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
                Stacks.SheafOfModules.overPullbackComp B.structureSheaf T.hom g.left)
              (restrictModule B S hS) ≪≫
            Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                (SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
                (restrictModule B S hS) ≪≫
              Functor.isoWhiskerLeft (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                  (objRestrictSectionsIso B S hS T) ≪≫
                (Functor.associator (SheafOfModules.overPullback.{u} B.structureSheaf g.left)
                  (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T))
                  (Scheme.Modules.pushforward (objHom B S hS T))).symm).symm

/-! ### The square and the pseudonaturality -/

/-- **The square for Stacks 03DV at a morphism follows from the cocycle for the comparison of
sections at that morphism.**  This is
`Stacks.Mates.trans_assoc_of_conjugate_of_mates` instantiated at the three
pullback–pushforward adjunctions of modules on schemes, the three associated-module adjunctions,
and the three adjunctions `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` of
restriction to an object.

Of its five mate hypotheses, three are `rfl` —
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` *is* the mate of Stacks 03DV with respect
to this family — the mate of the contraction of the iterated pullback of modules on schemes is
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_pullbackComp_objHom`, and the mate of the
functoriality of restriction to an object is
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp`. -/
public theorem natIsoCompSquare_of_sectionsCocycle {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (h : SectionsCocycle B S hS g) :
    NatIsoCompSquare B hS g :=
  Stacks.Mates.trans_assoc_of_conjugate_of_mates
    (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T))
    (Scheme.Modules.pullbackPushforwardAdjunction
      (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)))
    (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T'))
    (associatedModuleAdjunction B S hS)
    (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T))
    (associatedModuleAdjunction B (objScheme B S hS T') (contains_objScheme B S hS T'))
    (objRestrictOverPullbackAdjunction B S hS T)
    (objRestrictOverPullbackAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left))
    (objRestrictOverPullbackAdjunction B S hS T')
    (Scheme.Modules.pullbackComp
        (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
        (objHom B S hS T) ≪≫
      Scheme.Modules.pullbackCongr (objHom_comp B S hS g))
    (associatedModuleObjRestrictNatIso B S hS T)
    (associatedModuleObjRestrictNatIso B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left))
    (associatedModuleObjRestrictNatIso B S hS T')
    (objRestrictComp B S hS g)
    (conjugateIsoEquiv_pullbackComp_objHom B S hS g) rfl rfl rfl
    (conjugateIsoEquiv_objRestrictComp B S hS g) h

/-- **The comparison isomorphism of Stacks 03DV is pseudonatural as soon as the cocycle for the
comparison of sections holds at every base.**  This is
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` — the residue of Stacks 03DX (1),
and the hypothesis every consumer of that tag in this library carries — reduced to one identity
between composites of pushforwards of sheaves of modules.

It is `AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural_of_natIsoCompSquare` with the
square supplied at every base by
`AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_sectionsCocycle`.  As there, the hypothesis is
quantified over an arbitrary base of the site because the instance the assembly consumes is at the
base `AlgebraicGeometry.BigFppfOver.objScheme` of `T`. -/
public theorem localComparisonPseudonatural_of_sectionsCocycle
    (h : ∀ {X : Scheme.{u}} (hX : B.Contains X) {W W' : BigFppfOver B X hX} (g : W' ⟶ W),
      SectionsCocycle B X hX g)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    LocalComparisonPseudonatural B S hS G :=
  localComparisonPseudonatural_of_natIsoCompSquare B S hS
    (fun {X : Scheme.{u}} (hX : B.Contains X) {W W' : BigFppfOver B X hX} (g : W' ⟶ W) =>
      natIsoCompSquare_of_sectionsCocycle B X hX g (h hX g)) G

end AlgebraicGeometry.BigFppfOver

end
