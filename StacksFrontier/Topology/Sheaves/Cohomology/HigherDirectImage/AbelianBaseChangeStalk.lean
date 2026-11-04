module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.InverseImageSquareSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperFiberStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# The underived base change morphism of abelian sheaves is an isomorphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commuting square of topological spaces in which, for every `y' : Y'`, the second projection
identifies the fibre `f'^{-1}(y')` with the fibre `f^{-1}(g y')`. This file proves that the
underived base change morphism

`g^{-1} f_* ⟶ f'_* (g')^{-1}`

of `Stacks.Cohomology.BaseChange.abelianSheafBaseChange` is then an isomorphism of functors on
abelian sheaves, provided both `f` and `f'` are closed with quasi-compact separated fibres.

## Main results

All in the namespace `Stacks.Cohomology.BaseChange`.

* `stalkFunctor_map_abelianSheafBaseChange_germ`: what the stalk of the base change morphism does
  to a germ, namely the section induced on the ambient inverse image, restricted along the
  commutativity of the square.
* `ambientStalkHom_comp_stalkFunctor_map_abelianSheafBaseChange`: the stalk of the base change
  morphism, composed with the stalk identifications for `g`, `f'` and the fibres, is the stalk
  identification for `f`.
* `isIso_abelianSheafBaseChange_app_of_fiberIso`,
  `isIso_abelianSheafBaseChange_of_fiberIso`: the base change morphism is an isomorphism, at one
  sheaf and as a transformation.

## References

* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Cohomology.BaseChange

universe u

/-- **The comparison of direct images supplied by an equality of maps of spaces is a restriction
map of the sheaf.** -/
private theorem pushforward_eqToIso_hom_app_hom_app {X' Y : TopCat.{u}} {k k' : X' ⟶ Y}
    (hk : k = k') (J : TopCat.Sheaf AddCommGrpCat.{u} X') (V : Opens Y)
    (h : (Opens.map k').obj V ≤ (Opens.map k).obj V) :
    ((eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) hk)).hom.app J).hom.app
        (op V) =
      J.presheaf.map (homOfLE h).op := by
  subst hk
  rw [show homOfLE h = 𝟙 ((Opens.map k).obj V) from Subsingleton.elim _ _]
  exact (CategoryTheory.Functor.map_id _ _).symm

/-- **Cancelling three invertible factors from a four-factor identity.** If `a ≫ b ≫ c = e` with
`a`, `c` and `e` isomorphisms, then `b` is an isomorphism. -/
private theorem isIso_of_fac_of_isIso {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (e : A ⟶ E)
    (ha : IsIso a) (hc : IsIso c) (he : IsIso e)
    (w : a ≫ b ≫ c = e) : IsIso b := by
  have := ha
  have := hc
  have hw : IsIso (a ≫ b ≫ c) := w ▸ he
  have hbc : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a _
  have hb : b = (b ≫ c) ≫ inv c := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hb]
  infer_instance

variable {X X' Y Y' : TopCat.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)

/-- **What the stalk of the base change morphism does to a germ.** The germ at `y'` of the stalk
of `g^{-1} f_* F` determined by a section `s` of `F` on `f^{-1}(V)` is carried to the germ at `y'`
of the section of `(g')^{-1} F` on `(g')^{-1} f^{-1}(V)` induced by `s`, restricted to
`(f')^{-1} g^{-1}(V)` — the two opens of `X'` agreeing by commutativity of the square. -/
theorem stalkFunctor_map_abelianSheafBaseChange_germ (comm : g' ≫ f = f' ≫ g)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) (y' : Y') (V : Opens Y)
    (hy : y' ∈ (Opens.map g).obj V)
    (hle : (Opens.map f').obj ((Opens.map g).obj V) ≤
      (Opens.map g').obj ((Opens.map f).obj V))
    (s : ToType (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I).presheaf.obj (op V))) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y').map
        ((abelianSheafBaseChange f f' g g' comm).app I).hom
        (Stacks.Topology.ambientStalkHom g
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I) y'
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I).presheaf.germ V
            ((g.hom : Y' → Y) y') hy s)) =
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I)).presheaf.germ
        ((Opens.map g).obj V) y' hy
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I).presheaf.map (homOfLE hle).op
          (Stacks.Topology.ambientSection g' I
            (le_refl ((Opens.map g').obj ((Opens.map f).obj V))) s)) := by
  have hstalk := (Stacks.Topology.germ_ambientSection g
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I)
    (le_refl ((Opens.map g).obj V)) y' hy s).symm
  have hfunctor := TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map g).obj V) y' hy
    ((abelianSheafBaseChange f f' g g' comm).app I).hom
    (Stacks.Topology.ambientSection g ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I)
      (le_refl ((Opens.map g).obj V)) s)
  have hunit := ConcreteCategory.congr_hom
    (abelianSheafBaseChange_hom_app_unit f f' g g' comm I V) s
  have hsrc := Stacks.Topology.ambientSection_eq_unit g
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I) V
  have htgt := Stacks.Topology.ambientSection_eq_unit g' I ((Opens.map f).obj V)
  have hcross := pushforward_eqToIso_hom_app_hom_app comm
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) V hle
  have key : ((abelianSheafBaseChange f f' g g' comm).app I).hom.app
        (op ((Opens.map g).obj V))
        (Stacks.Topology.ambientSection g
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I)
          (le_refl ((Opens.map g).obj V)) s) =
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I).presheaf.map (homOfLE hle).op
        (Stacks.Topology.ambientSection g' I
          (le_refl ((Opens.map g').obj ((Opens.map f).obj V))) s) := by
    refine Eq.trans (congrArg _ (ConcreteCategory.congr_hom hsrc s)) ?_
    refine Eq.trans (((ConcreteCategory.comp_apply _ _ s).symm.trans hunit).trans
      (ConcreteCategory.comp_apply _ _ s)) ?_
    exact Eq.trans (ConcreteCategory.congr_hom hcross _)
      (congrArg _ (ConcreteCategory.congr_hom htgt s).symm)
  exact (congrArg _ hstalk).trans (hfunctor.trans (congrArg _ key))

/-- **The base change morphism is the map the three stalk identifications produce.** With
`Z₁ = (f')^{-1}(y')` and `Z₂ = f^{-1}(g y')` their inclusions `ι₁`, `ι₂` and an isomorphism
`φ : Z₁ ≅ Z₂` induced by `g'`, the composite

`(f_* I)_{g y'} ⟶ (g^{-1} f_* I)_{y'} ⟶ (f'_*(g')^{-1}I)_{y'} ⟶ Γ(Z₁, ι₁^{-1}(g')^{-1}I)
  ⟶ Γ(Z₂, ι₂^{-1}I)`

of the stalk comparison of the inverse image, the stalk of the base change morphism, the
fibre-sections comparison for `f'` and the comparison of the two fibres is the fibre-sections
comparison for `f`. -/
theorem ambientStalkHom_comp_stalkFunctor_map_abelianSheafBaseChange (comm : g' ≫ f = f' ≫ g)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) (y' : Y')
    (φ : TopCat.of ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≅
      TopCat.of ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
    (hcomm : Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≫ g' =
      φ.hom ≫ Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y))) :
    Stacks.Topology.ambientStalkHom g ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I) y' ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y').map
          ((abelianSheafBaseChange f f' g g' comm).app I).hom ≫
        Stacks.Topology.fiberStalkSectionsMap f' y'
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) ≫
        (Stacks.Topology.squareSectionsIso
          (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y'))) g' φ
          (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
          hcomm I).hom =
      Stacks.Topology.fiberStalkSectionsMap f ((g.hom : Y' → Y) y') I := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hxV => ConcreteCategory.hom_ext _ _ fun s => ?_
  have hy : y' ∈ (Opens.map g).obj V := hxV
  have hle : (Opens.map f').obj ((Opens.map g).obj V) ≤
      (Opens.map g').obj ((Opens.map f).obj V) :=
    le_of_eq (congrArg (fun k : X' ⟶ Y => (Opens.map k).obj V) comm).symm
  have htopB : (⊤ : Opens (TopCat.of ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))) ≤
      (Opens.map (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))).obj
        ((Opens.map f').obj ((Opens.map g).obj V)) :=
    Stacks.Topology.top_le_map_openNhdsSet
      ((Stacks.Topology.preimageNeighborhoodFunctor f' y').obj
        (op ⟨(Opens.map g).obj V, hy⟩)).unop
  have htopA : (⊤ : Opens (TopCat.of ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))) ≤
      (Opens.map (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))).obj
        ((Opens.map g').obj ((Opens.map f).obj V)) := fun _ hz => hle (htopB hz)
  have htop₂ : (⊤ : Opens (TopCat.of ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))) ≤
      (Opens.map (Stacks.subsetInclusion X
        ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))).obj ((Opens.map f).obj V) :=
    Stacks.Topology.top_le_map_openNhdsSet
      ((Stacks.Topology.preimageNeighborhoodFunctor f ((g.hom : Y' → Y) y')).obj
        (op ⟨V, hy⟩)).unop
  have hbc := stalkFunctor_map_abelianSheafBaseChange_germ f f' g g' comm I y' V hy hle s
  have hfibre := Stacks.Topology.fiberStalkSectionsMap_germ f' y'
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) ((Opens.map g).obj V) hy
    (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I).presheaf.map (homOfLE hle).op
      (Stacks.Topology.ambientSection g' I
        (le_refl ((Opens.map g').obj ((Opens.map f).obj V))) s))
  have hbase := Stacks.Topology.fiberStalkSectionsMap_germ f ((g.hom : Y' → Y) y') I V hy s
  have hsquare := Stacks.Topology.ambientSection_comp_squareSectionsIso
    (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y'))) g' φ
    (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
    hcomm I ((Opens.map f).obj V) htopA htop₂
  have hshrink := Stacks.Topology.ambientSection_map_apply
    (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) (homOfLE hle) htopB htopA
    (Stacks.Topology.ambientSection g' I
      (le_refl ((Opens.map g').obj ((Opens.map f).obj V))) s)
  have hclose : (Stacks.Topology.squareSectionsIso
        (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y'))) g' φ
        (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
        hcomm I).hom
      (Stacks.Topology.ambientSection
        (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) htopA
        (Stacks.Topology.ambientSection g' I
          (le_refl ((Opens.map g').obj ((Opens.map f).obj V))) s)) =
      Stacks.Topology.ambientSection
        (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
        I htop₂ s :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.comp_apply _ _ s).symm.trans (ConcreteCategory.congr_hom hsquare s))
  refine Eq.trans (ConcreteCategory.comp_apply _ _ s) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ s).symm
  refine Eq.trans (congrArg
    (fun z => (Stacks.Topology.squareSectionsIso
      (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y'))) g' φ
      (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
      hcomm I).hom z)
    (Eq.trans (congrArg (fun z => Stacks.Topology.fiberStalkSectionsMap f' y'
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I) z) hbc)
      (hfibre.trans hshrink))) ?_
  exact hclose.trans hbase.symm

/-- **The underived base change morphism is an isomorphism at every abelian sheaf.** For a
commuting square in which both `f` and `f'` are closed with quasi-compact separated fibres and in
which the second projection identifies each fibre of `f'` with the corresponding fibre of `f`,
the morphism `g^{-1} f_* I ⟶ f'_*(g')^{-1} I` is an isomorphism. -/
theorem isIso_abelianSheafBaseChange_app_of_fiberIso (comm : g' ≫ f = f' ≫ g)
    (hclosed : IsClosedMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (hclosed' : IsClosedMap (f'.hom : X' → Y')) (hsep' : IsSeparatedMap (f'.hom : X' → Y'))
    (hcompact : ∀ y : Y, IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
    (hcompact' : ∀ y' : Y', IsCompact ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))
    (φ : ∀ y' : Y', TopCat.of ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≅
      TopCat.of ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
    (hcomm : ∀ y' : Y',
      Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≫ g' =
        (φ y').hom ≫
          Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsIso ((abelianSheafBaseChange f f' g g' comm).app I) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro y'
  have hkey := ambientStalkHom_comp_stalkFunctor_map_abelianSheafBaseChange f f' g g' comm I y'
    (φ y') (hcomm y')
  have hfirst : IsIso (Stacks.Topology.ambientStalkHom g
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj I) y') :=
    Stacks.Topology.isIso_ambientStalkHom g _ y'
  have hthird : IsIso (Stacks.Topology.fiberStalkSectionsMap f' y'
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g').obj I)) :=
    Stacks.Topology.isIso_fiberStalkSectionsMap f' y' hclosed' (hcompact' y') hsep' _
  have hfourth : IsIso (Stacks.Topology.squareSectionsIso
      (Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y'))) g' (φ y')
      (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
      (hcomm y') I).hom :=
    Iso.isIso_hom _
  have hright : IsIso (Stacks.Topology.fiberStalkSectionsMap f ((g.hom : Y' → Y) y') I) :=
    Stacks.Topology.isIso_fiberStalkSectionsMap f ((g.hom : Y' → Y) y') hclosed
      (hcompact _) hsep I
  exact isIso_of_fac_of_isIso _ _ _ _ hfirst (IsIso.comp_isIso' hthird hfourth) hright hkey

/-- **The underived base change morphism is an isomorphism of functors**, under the hypotheses of
`isIso_abelianSheafBaseChange_app_of_fiberIso`. -/
theorem isIso_abelianSheafBaseChange_of_fiberIso (comm : g' ≫ f = f' ≫ g)
    (hclosed : IsClosedMap (f.hom : X → Y)) (hsep : IsSeparatedMap (f.hom : X → Y))
    (hclosed' : IsClosedMap (f'.hom : X' → Y')) (hsep' : IsSeparatedMap (f'.hom : X' → Y'))
    (hcompact : ∀ y : Y, IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
    (hcompact' : ∀ y' : Y', IsCompact ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')))
    (φ : ∀ y' : Y', TopCat.of ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≅
      TopCat.of ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y)))
    (hcomm : ∀ y' : Y',
      Stacks.subsetInclusion X' ((f'.hom : X' → Y') ⁻¹' ({y'} : Set Y')) ≫ g' =
        (φ y').hom ≫
          Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({(g.hom : Y' → Y) y'} : Set Y))) :
    IsIso (abelianSheafBaseChange f f' g g' comm) :=
  have : ∀ I : TopCat.Sheaf AddCommGrpCat.{u} X,
      IsIso ((abelianSheafBaseChange f f' g g' comm).app I) := fun I =>
    isIso_abelianSheafBaseChange_app_of_fiberIso f f' g g' comm hclosed hsep hclosed' hsep'
      hcompact hcompact' φ hcomm I
  NatIso.isIso_of_isIso_app _

end Stacks.Cohomology.BaseChange

end
