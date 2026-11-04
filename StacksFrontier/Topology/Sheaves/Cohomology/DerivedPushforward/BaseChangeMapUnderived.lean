module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The derived base change map on the class of a complex

A commutative square of ringed spaces

```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```

has two base change maps: the derived one `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` of Tag 08HY, and the
underived one `g^* (f_* K) ⟶ f'_* (g'^* K)` on the homotopy categories, the mate of the
composition isomorphisms of degreewise pullback.  At the class `Qh W` of a complex the two are
related by the canonical comparisons of derived and underived functors: the square

```
Lg^* (Qh (f_* W)) ----------------------------> Qh (g^* (f_* W))
      |                                                |
Lg^* (Rf_* (Qh W))                              Qh (f'_* (g'^* W))
      |                                                |
Rf'_* (Lg'^* (Qh W)) --------------------------> Rf'_* (Qh (g'^* W))
```

commutes, the horizontal arrows being the comparisons of `Lg^*` and of `Lg'^*`, the left vertical
arrows the comparison of `Rf_*` followed by the derived base change map, and the right vertical
arrows the underived base change map followed by the comparison of `Rf'_*`.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.underivedBaseChangeSquare`: the underived base change map
  `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` on the homotopy categories, as a mate.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoS`: the composition isomorphism of
  Tag 0D5S with its derived-category arguments spelled over
  `SheafOfModules (structureSheafRing _)`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.Mate.comparison_comp_mateEquiv_app`: the square above for
  arbitrary adjunctions, comparisons and composition isomorphisms satisfying the counit
  factorizations of the two derived adjunctions and the factorizations of the two composition
  isomorphisms.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_Qh_comparison`: the square above for
  the canonical derived functors of a commutative square of ringed spaces.

## Implementation notes

*Why the abstract form.*  The canonical derived functors are `abbrev`s over total derived
functors, and a goal mentioning several of them at once is expensive to rewrite in.  The square is
therefore proved once with every functor, adjunction and comparison a variable, and the canonical
statement is a single application of it: the four compatibilities are Tag 079W's counit
factorization for `f` and for `f'` and Tag 0D5S's factorization of the composition comparison at
`(f', g)` and at `(g', f)`.  The transport along the commutativity of the square, which the
canonical base change map carries as an `eqToIso`, is absorbed inside the abstract statement by
substitution (`Mate.comparison_comp_derivedBaseChangeMap_of_eq`).

*Why `derivedPullbackCompIsoS`.*
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` takes its derived categories
over `ModuleSheaves`, while the derived pullbacks and their comparisons take them over
`SheafOfModules (structureSheafRing _)`.  The two are definitionally equal, but a statement mixing
the two spellings is expensive for the kernel to check; supplying the instances explicitly in the
second spelling keeps every statement below in one spelling.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedPushforwardComposition

namespace Stacks.Cohomology.DerivedBaseChange

noncomputable section

namespace Mate

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {KX' : Type u₁} {KX : Type u₂} {KS' : Type u₃} {KS : Type u₄}
  {DX' : Type u₅} {DX : Type u₆} {DS' : Type u₇} {DS : Type u₈}
  [Category.{v₁} KX'] [Category.{v₂} KX] [Category.{v₃} KS'] [Category.{v₄} KS]
  [Category.{v₅} DX'] [Category.{v₆} DX] [Category.{v₇} DS'] [Category.{v₈} DS]
  {QX' : KX' ⥤ DX'} {QX : KX ⥤ DX} {QS' : KS' ⥤ DS'} {QS : KS ⥤ DS}
  {uf : KS ⥤ KX} {ug : KS ⥤ KS'} {uf' : KS' ⥤ KX'} {ug' : KX ⥤ KX'} {uc : KS ⥤ KX'}
  {pf : KX ⥤ KS} {pf' : KX' ⥤ KS'}
  {Lf : DS ⥤ DX} {Lg : DS ⥤ DS'} {Lf' : DS' ⥤ DX'} {Lg' : DX ⥤ DX'} {Lc : DS ⥤ DX'}
  {Rf : DX ⥤ DS} {Rf' : DX' ⥤ DS'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (uadjf : uf ⊣ pf) (uadjf' : uf' ⊣ pf')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (ueg : ug ⋙ uf' ≅ uc) (uef : uf ⋙ ug' ≅ uc)
  (αf : QS ⋙ Lf ⟶ uf ⋙ QX) (αg : QS ⋙ Lg ⟶ ug ⋙ QS') (αf' : QS' ⋙ Lf' ⟶ uf' ⋙ QX')
  (αg' : QX ⋙ Lg' ⟶ ug' ⋙ QX') (αc : QS ⋙ Lc ⟶ uc ⋙ QX')
  (ηf : pf ⋙ QS ⟶ QX ⋙ Rf) (ηf' : pf' ⋙ QS' ⟶ QX' ⋙ Rf')

omit [Category.{v₁} KX'] [Category.{v₂} KX] [Category.{v₃} KS'] [Category.{v₄} KS]
  [Category.{v₅} DX'] [Category.{v₆} DX] [Category.{v₇} DS'] [Category.{v₈} DS] in
/-- The component of a two-square built by `TwoSquare.mk` is the component of the natural
transformation it is built from. -/
theorem twoSquare_mk_app {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (α : T ⋙ R ⟶ L ⋙ B) (X : C₁) :
    (TwoSquare.mk T L R B α).app X = α.app X :=
  rfl

/-- The composite of `ef⁻¹`, `Lg'` of the comparison for `Lf` and the comparison for `Lg'` is the
comparison for `Lc` followed by the class of `uef⁻¹`: the factorization `hef` solved for the
inverse of `ef`. -/
theorem inv_app_comp_comparison
    (hef : ∀ V, ef.hom.app (QS.obj V) ≫ αc.app V =
      Lg'.map (αf.app V) ≫ αg'.app (uf.obj V) ≫ QX'.map (uef.hom.app V)) (V : KS) :
    ef.inv.app (QS.obj V) ≫ Lg'.map (αf.app V) ≫ αg'.app (uf.obj V) =
      αc.app V ≫ QX'.map (uef.inv.app V) := by
  rw [← cancel_epi (ef.hom.app (QS.obj V)), Iso.hom_inv_id_app_assoc, reassoc_of% (hef V),
    ← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- **The derived base change map on the class of a complex**, for arbitrary adjunctions
`Lf ⊣ Rf`, `Lf' ⊣ Rf'` lifting `uf ⊣ pf`, `uf' ⊣ pf'` along `QX`, `QX'`, `QS`, `QS'`, and
composition isomorphisms `eg`, `ef` lifting `ueg`, `uef`.  The four hypotheses are the counit
factorizations of the two derived adjunctions and the factorizations of the two composition
isomorphisms through the comparisons. -/
theorem comparison_comp_mateEquiv_app
    (hεf : ∀ W, Lf.map (ηf.app W) ≫ adjf.counit.app (QX.obj W) =
      αf.app (pf.obj W) ≫ QX.map (uadjf.counit.app W))
    (hεf' : ∀ W, Lf'.map (ηf'.app W) ≫ adjf'.counit.app (QX'.obj W) =
      αf'.app (pf'.obj W) ≫ QX'.map (uadjf'.counit.app W))
    (heg : ∀ V, eg.hom.app (QS.obj V) ≫ αc.app V =
      Lf'.map (αg.app V) ≫ αf'.app (ug.obj V) ≫ QX'.map (ueg.hom.app V))
    (hef : ∀ V, ef.hom.app (QS.obj V) ≫ αc.app V =
      Lg'.map (αf.app V) ≫ αg'.app (uf.obj V) ≫ QX'.map (uef.hom.app V))
    (W : KX) :
    Lg.map (ηf.app W) ≫
        (mateEquiv adjf adjf' (TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv))).app (QX.obj W) ≫
          Rf'.map (αg'.app W) =
      αg.app (pf.obj W) ≫
        QS'.map ((mateEquiv uadjf uadjf' (TwoSquare.mk _ _ _ _ (ueg.hom ≫ uef.inv))).app W) ≫
          ηf'.app (ug'.obj W) := by
  apply (adjf'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [Adjunction.counit_naturality, reassoc_of% (mateEquiv_counit adjf adjf'
      (TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv)) (QX.obj W)),
    hεf']
  have h5 :=
    αf'.naturality ((mateEquiv uadjf uadjf' (TwoSquare.mk _ _ _ _ (ueg.hom ≫ uef.inv))).app W)
  have h1 := eg.hom.naturality (ηf.app W)
  have h2 := ef.inv.naturality (ηf.app W)
  have h3 := αg'.naturality (uadjf.counit.app W)
  simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h1 h2 h3 h5
  rw [twoSquare_mk_app, NatTrans.comp_app]
  simp only [Category.assoc, Functor.comp_obj]
  rw [reassoc_of% h1, reassoc_of% h2, ← Functor.map_comp_assoc, hεf, Functor.map_comp_assoc, h3,
    reassoc_of% (inv_app_comp_comparison ef uef αf αg' αc hef), reassoc_of% (heg _),
    reassoc_of% h5]
  have h4 := mateEquiv_counit uadjf uadjf' (TwoSquare.mk _ _ _ _ (ueg.hom ≫ uef.inv)) W
  rw [twoSquare_mk_app, NatTrans.comp_app] at h4
  simp only [← Functor.map_comp, h4, Category.assoc]

section DerivedTyped

attribute [local instance] HasDerivedCategory.standard

universe u

variable {X' X S' S : RingedSpace.{u, u}}
  {KX'' : Type u₁} {KX₀ : Type u₂} {KS'' : Type u₃} {KS₀ : Type u₄}
  [Category.{v₁} KX''] [Category.{v₂} KX₀] [Category.{v₃} KS''] [Category.{v₄} KS₀]
  {QX'' : KX'' ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {QX₀ : KX₀ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {QS'' : KS'' ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {QS₀ : KS₀ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {vf : KS₀ ⥤ KX₀} {vg : KS₀ ⥤ KS''} {vf' : KS'' ⥤ KX''} {vg' : KX₀ ⥤ KX''} {vc : KS₀ ⥤ KX''}
  {qf : KX₀ ⥤ KS₀} {qf' : KX'' ⥤ KS''}
  {Mf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Mg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Mf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Mg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Mc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Nf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Nf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}

/-- `comparison_comp_mateEquiv_app` for the derived base change map, with the composition
isomorphism `dg` of the form
`dg₀ ≪≫ eqToIso (congrArg M e)`, where `M` is a family of functors with comparisons `βM`: the
compatibility of `dg` with the comparisons is derived from that of `dg₀`, by substituting `e`. -/
theorem comparison_comp_derivedBaseChangeMap_of_eq {T : Sort*}
    (M : T → (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))))
    (v : T → (KS₀ ⥤ KX'')) (βM : ∀ t, QS₀ ⋙ M t ⟶ v t ⋙ QX'') {t₀ t₁ : T} (e : t₀ = t₁)
    (bdf : Mf ⊣ Nf) (bdf' : Mf' ⊣ Nf') (vadjf : vf ⊣ qf) (vadjf' : vf' ⊣ qf')
    (dg₀ : Mg ⋙ Mf' ≅ M t₀) (df : Mf ⋙ Mg' ≅ M t₁) (veg₀ : vg ⋙ vf' ≅ v t₀)
    (vef : vf ⋙ vg' ≅ v t₁)
    (βf : QS₀ ⋙ Mf ⟶ vf ⋙ QX₀) (βg : QS₀ ⋙ Mg ⟶ vg ⋙ QS'') (βf' : QS'' ⋙ Mf' ⟶ vf' ⋙ QX'')
    (βg' : QX₀ ⋙ Mg' ⟶ vg' ⋙ QX'')
    (θf : qf ⋙ QS₀ ⟶ QX₀ ⋙ Nf) (θf' : qf' ⋙ QS'' ⟶ QX'' ⋙ Nf')
    (hεf : ∀ W, Mf.map (θf.app W) ≫ bdf.counit.app (QX₀.obj W) =
      βf.app (qf.obj W) ≫ QX₀.map (vadjf.counit.app W))
    (hεf' : ∀ W, Mf'.map (θf'.app W) ≫ bdf'.counit.app (QX''.obj W) =
      βf'.app (qf'.obj W) ≫ QX''.map (vadjf'.counit.app W))
    (heg₀ : ∀ V, dg₀.hom.app (QS₀.obj V) ≫ (βM t₀).app V =
      Mf'.map (βg.app V) ≫ βf'.app (vg.obj V) ≫ QX''.map (veg₀.hom.app V))
    (hef : ∀ V, df.hom.app (QS₀.obj V) ≫ (βM t₁).app V =
      Mg'.map (βf.app V) ≫ βg'.app (vf.obj V) ≫ QX''.map (vef.hom.app V))
    (W : KX₀) :
    Mg.map (θf.app W) ≫
        derivedBaseChangeMap bdf bdf' (dg₀ ≪≫ eqToIso (congrArg M e)) df (QX₀.obj W) ≫
          Nf'.map (βg'.app W) =
      βg.app (qf.obj W) ≫
        QS''.map ((mateEquiv vadjf vadjf' (TwoSquare.mk _ _ _ _
          ((veg₀ ≪≫ eqToIso (congrArg v e)).hom ≫ vef.inv))).app W) ≫
          θf'.app (vg'.obj W) := by
  subst e
  simp only [eqToIso_refl, Iso.trans_refl]
  exact comparison_comp_mateEquiv_app bdf bdf' vadjf vadjf' dg₀ df veg₀ vef βf βg βf' βg'
    (βM t₀) θf θf' hεf hεf' heg₀ hef W

end DerivedTyped

end Mate

section Canonical

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Tag 0D5S, with its derived-category
arguments spelled over `SheafOfModules (structureSheafRing _)`, the spelling of the derived
pullbacks and of their comparisons. -/
abbrev derivedPullbackCompIsoS {X₁ X₂ X₃ : RingedSpace.{u, u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) :
    derivedPullback f₂ ⋙ derivedPullback f₁ ≅ derivedPullback (f₁ ≫ f₂) :=
  @derivedPullbackCompIsoCanonical X₁ X₂ X₃ f₁ f₂
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X₁)))
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X₂)))
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X₃)))

/-- The factorization of `derivedPullbackCompIsoS` through the comparisons. -/
theorem derivedPullbackCompIsoS_hom_app_comp_comparison {X₁ X₂ X₃ : RingedSpace.{u, u}}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (V : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X₃)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompIsoS f₁ f₂).hom.app (DerivedCategory.Qh.obj V) ≫
        (derivedPullbackComparison (f₁ ≫ f₂)).app V =
      (derivedPullback f₁).map ((derivedPullbackComparison f₂).app V) ≫
        (derivedPullbackComparison f₁).app
          (((modulePullback f₂).mapHomotopyCategory (ComplexShape.up ℤ)).obj V) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f₁ f₂).hom.app V) :=
  derivedPullbackCompIsoCanonical_hom_app_comp_comparison f₁ f₂ V

/-- The composite `g^* ⋙ f'^*` of degreewise pullbacks on the homotopy categories, down the left
and along the bottom of the square, identified with degreewise pullback along `g' ≫ f`. -/
def pullbackOnHomotopyCompIsoLeft :
    (modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePullback f').mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (modulePullback (g' ≫ f)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  pullbackOnHomotopyCompIso f' g ≪≫
    eqToIso (congrArg (fun h : X' ⟶ S =>
      (modulePullback h).mapHomotopyCategory (ComplexShape.up ℤ)) sq.symm)

/-- **The underived base change map** `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` on the unbounded homotopy
categories of a commutative square of ringed spaces: the mate, under the degreewise adjunctions
`f^* ⊣ f_*` and `f'^* ⊣ f'_*`, of the comparison of the two composites of degreewise pullbacks. -/
def underivedBaseChangeSquare :
    TwoSquare ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward f').mapHomotopyCategory (ComplexShape.up ℤ)) :=
  mateEquiv (homotopyPullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction f')
    (TwoSquare.mk _ _ _ _ ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom ≫
      (pullbackOnHomotopyCompIso g' f).inv))

/-- `pullbackOnHomotopyCompIsoLeft`, unfolded. -/
theorem pullbackOnHomotopyCompIsoLeft_eq :
    pullbackOnHomotopyCompIsoLeft g' f' f g sq = pullbackOnHomotopyCompIso f' g ≪≫
    eqToIso (congrArg (fun h : X' ⟶ S =>
      (modulePullback h).mapHomotopyCategory (ComplexShape.up ℤ)) sq.symm) := rfl

/-- `underivedBaseChangeSquare` is the mate of the composite of the two composition isomorphisms
of degreewise pullback. -/
theorem underivedBaseChangeSquare_eq :
    underivedBaseChangeSquare g' f' f g sq =
      mateEquiv (homotopyPullbackPushforwardAdjunction f)
        (homotopyPullbackPushforwardAdjunction f')
        (TwoSquare.mk _ _ _ _ ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom ≫
          (pullbackOnHomotopyCompIso g' f).inv)) :=
  rfl

/-- The derived base change map, with both composition isomorphisms written through
`derivedPullbackCompIsoS`. -/
theorem derivedBaseChangeMap_eq_mate
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K = Mate.derivedBaseChangeMap (derivedAdjunction f)
      (derivedAdjunction f') (derivedPullbackCompIsoS f' g ≪≫
        eqToIso (congrArg (fun h : X' ⟶ S => derivedPullback h) sq.symm))
      (derivedPullbackCompIsoS g' f) K :=
  rfl

/-- **The derived base change map on the class of a complex.**  For a commutative square of
ringed spaces and a complex `W` of `𝒪_X`-modules, the derived base change map at `Qh W`, preceded
by `Lg^*` of the comparison `Qh (f_* W) ⟶ Rf_* (Qh W)` and followed by `Rf'_*` of the comparison
`Lg'^* (Qh W) ⟶ Qh (g'^* W)`, is the comparison `Lg^* (Qh (f_* W)) ⟶ Qh (g^* (f_* W))` followed by
the class of the underived base change map and the comparison
`Qh (f'_* (g'^* W)) ⟶ Rf'_* (Qh (g'^* W))`. -/
theorem derivedBaseChangeMap_Qh_comparison
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback g).map ((derivedPushforwardUnit f).app W) ≫
        derivedBaseChangeMap g' f' f g sq (DerivedCategory.Qh.obj W) ≫
          (derivedPushforward f').map ((derivedPullbackComparison g').app W) =
      (derivedPullbackComparison g).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((underivedBaseChangeSquare g' f' f g sq).app W) ≫
          (derivedPushforwardUnit f').app
            (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj W) := by
  rw [derivedBaseChangeMap_eq_mate, underivedBaseChangeSquare_eq, pullbackOnHomotopyCompIsoLeft_eq]
  exact Mate.comparison_comp_derivedBaseChangeMap_of_eq (fun h : X' ⟶ S => derivedPullback h)
    (fun h : X' ⟶ S => (modulePullback h).mapHomotopyCategory (ComplexShape.up ℤ))
    (fun h : X' ⟶ S => derivedPullbackComparison h) sq.symm
    (derivedAdjunction f) (derivedAdjunction f')
    (homotopyPullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction f')
    (derivedPullbackCompIsoS f' g) (derivedPullbackCompIsoS g' f)
    (pullbackOnHomotopyCompIso f' g) (pullbackOnHomotopyCompIso g' f)
    (derivedPullbackComparison f) (derivedPullbackComparison g) (derivedPullbackComparison f')
    (derivedPullbackComparison g')
    (derivedPushforwardUnit f) (derivedPushforwardUnit f')
    (derivedAdjunction_counit_fac f) (derivedAdjunction_counit_fac f')
    (derivedPullbackCompIsoS_hom_app_comp_comparison f' g)
    (derivedPullbackCompIsoS_hom_app_comp_comparison g' f) W

end Canonical

end

end Stacks.Cohomology.DerivedBaseChange

end
