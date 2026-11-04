module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsFactorFourReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTranspose
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentBaseChangeComp

/-!
# The base change of Stacks 03LC (1) on sections over the final object

`AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat`, carried as a stand-in by
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsFactorFourReduction.lean`, asks
for a compatibility on sections over the final object of the small étale site between the
base-change identification `(k^*𝓖)^a ≅ ε_ψ^*(𝓖^a)` of **Stacks 03LC (1)** and the base change of
the presheaf of **Stacks 03DS**.  Both sides of that equation become comparable after the
*invertible prefix* `AlgebraicGeometry.Stack.unitFinalPrefix`: the unit of the associated-module
adjunction of **Stacks 03DU (4)** over the open `⊤`, followed by the identification
`AlgebraicGeometry.SmallEtale.restrictModuleSectionsTopIso` of the sections of a restriction over
`⊤` with the sections over the final object.  That prefix may be cancelled, by
`AlgebraicGeometry.SmallEtale.isIso_sectionsUnit`.

This file proves that compatibility, so nothing carries it any more:
`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`.  The two sides, with
the prefix in place, are Lemma A — the Stacks 03LC (1) side — and Lemma B — the Stacks 03DS
side.

## Lemma A: the Stacks 03LC (1) side

`AlgebraicGeometry.Stack.unitFinal_comp_bcIso`: prefixing the identification
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` of Stacks 03LC (1) — read on
sections over the final object through `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` and
the sheafification unit — by the invertible prefix at `z` gives the unit of
pullback--pushforward for the morphism of schemes below `ψ`, followed by the invertible prefix at
`z'`.  Three ingredients go into it:

* the passage from the pullback of presheaves of modules of **Stacks 06WC** to the pullback along
  the structure map of `ε_ψ`, which is
  `Stacks.PresheafOfModules.homEquiv_pullbackCongr_hom_app_comp`, the mirror of
  `Stacks.PresheafOfModules.homEquiv_pullbackCongr_inv_app_comp`, together with
  `SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app`: together they
  compute the transpose of the identification, which is
  `AlgebraicGeometry.Stack.homEquiv_pullback_bcIso`;
* `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp`, which reads that transpose on
  sections over the final object;
* `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_inv_unit_sections_top`, the
  conjugacy which pins Stacks 03LC (1) on sections over the open `⊤`, transported to the final
  object by `AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop` and
  `AlgebraicGeometry.SmallEtale.finalToBaseChangeFinal_comp_baseChangeOpensIso_inv_app_top`.

## Lemma B: the Stacks 03DS side

`AlgebraicGeometry.Stack.step3_pullbackSections`: the identity

`u_a ≫ s_{z'} ≫ r_{z'} = s_z ≫ r_z ≫ Γ(n) ≫ bc`,

where `s_y` is `AlgebraicGeometry.Stack.sectionsUnitTop` — pulling a global section of the module
back to the open subscheme `⊤` — and `r_y` is the restriction map of the presheaf of Stacks 03DS
along `AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop`, `Γ(n)` is the restriction along the
arrow `n` of `Sch/W` below `ψ` and `bc` is
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` read through
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` and
`AlgebraicGeometry.Scheme.Modules.pullbackSection_top`.  Those three are statements about the
*values* of maps of sections, and neither side of the identity above may be read on values: the
two spellings of the sections over the final object -- `Γ(-, ⊤)` and
`AlgebraicGeometry.quasiCoherentPresheafFunctor` -- present their abelian group through
different instance paths, so `CategoryTheory.comp_apply` does not fire across the junction. The
three readings are therefore hoisted to equalities of *maps* first, on a pair of abstract
schemes and slice objects, in the section `Stacks.Sites` of this file:
`Stacks.Sites.pullbackSectionHom_comp_pullbackSectionsMap`,
`Stacks.Sites.pullbackSectionHom_comp_pullbackSectionHom` and
`Stacks.Sites.unitTop_eq_pullbackSectionHom`.  They assemble into
`Stacks.Sites.pullbackSectionHom_comp_quasiCoherentPresheafBaseChangeIso`, of which Lemma B is
the instance at the two final objects: `AlgebraicGeometry.Stack.sectionsUnitTop` is by
construction `AlgebraicGeometry.pullbackSectionHom` along the inclusion of the open `⊤`, which
is the structure morphism of `AlgebraicGeometry.SmallEtale.opensObj` at `⊤`.

No Stacks tag is registered: everything here rearranges statements whose mathematics is
attributed where it is proved.

## Main results

* `Stacks.PresheafOfModules.homEquiv_pullbackCongr_hom_app_comp`: the adjunct of a morphism out of
  a pullback of presheaves of modules, precomposed with the comparison of the pullbacks along two
  equal maps of presheaves of rings.
* `Stacks.Sites.pullbackSectionHom_comp_pullbackSectionHom`: **the composition law for pulling
  global sections back**, as an equality of maps of global sections.
* `Stacks.Sites.pullbackSectionHom_comp_quasiCoherentPresheafBaseChangeIso`: **pulling a global
  section back in one step or in two agrees on the presheaf of Stacks 03DS.**
* `AlgebraicGeometry.SmallEtale.unitTop_comp_associatedModulePresheafIso`: the unit of the
  associated-module adjunction over an open, read through the Stacks 070S identification.
* `AlgebraicGeometry.Stack.homEquiv_pullback_bcIso`: **the transpose of the Stacks 03LC (1)
  identification of Stacks 06WC form.**
* `AlgebraicGeometry.Stack.unitFinal_comp_bcIso`: **the Stacks 03LC (1) side of the
  compatibility.**
* `AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`: **the compatibility,
  which nothing carries any more.**

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u v w


/-- **Cancelling a prefix which splits as two split epimorphisms.**  The prefix is `uT ≫ rt`;
`rt` has the left inverse `rti`, and `uT` becomes the split epimorphism `sU` after the invertible
`ap`. -/
theorem Stacks.CategoryTheory.eq_of_split_prefix_comp_eq {C : Type*} [Category C]
    {A Bu Bo Q X : C} {pre : A ⟶ Bo} {uT : A ⟶ Bu} {rt : Bu ⟶ Bo} (rti : Bo ⟶ Bu)
    (sU : A ⟶ Q) (su : Q ⟶ A) (ap : Bu ⟶ Q) (api : Q ⟶ Bu)
    (hpre : pre = uT ≫ rt) (hrt : rti ≫ rt = 𝟙 Bo) (hsu : su ≫ sU = 𝟙 Q)
    (hap : ap ≫ api = 𝟙 Bu) (hfac : uT ≫ ap = sU)
    {L R : Bo ⟶ X} (hw : pre ≫ L = pre ≫ R) : L = R := by
  have hsp : su ≫ uT = api := by
    rw [← Category.comp_id (su ≫ uT), ← hap]
    simp only [Category.assoc, reassoc_of% hfac, reassoc_of% hsu]
  have hs : (rti ≫ ap ≫ su) ≫ pre = 𝟙 Bo := by
    rw [hpre]
    simp only [Category.assoc, reassoc_of% hsp, reassoc_of% hap, hrt]
  rw [← Category.id_comp L, ← Category.id_comp R, ← hs, Category.assoc, Category.assoc, hw]
  simp only [Category.assoc]

/-- Cancelling the forward map of an isomorphism on the left. -/
theorem Stacks.CategoryTheory.eq_of_iso_hom_comp_eq {C : Type*} [Category C] {A Bo X : C}
    (e : A ≅ Bo) {L R : Bo ⟶ X} (hw : e.hom ≫ L = e.hom ≫ R) : L = R :=
  (cancel_epi e.hom).1 hw

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- mirror of `homEquiv_pullbackCongr_inv_app_comp` -/
public theorem homEquiv_pullbackCongr_hom_app_comp {a b : S ⟶ F.op ⋙ R} (hab : a = b)
    [(_root_.PresheafOfModules.pushforward.{u} a).IsRightAdjoint]
    [(_root_.PresheafOfModules.pushforward.{u} b).IsRightAdjoint]
    (X : _root_.PresheafOfModules.{u} S) (Y : _root_.PresheafOfModules.{u} R)
    (f : (_root_.PresheafOfModules.pullback.{u} b).obj X ⟶ Y) :
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a).homEquiv X Y
        ((_root_.PresheafOfModules.pullbackCongr hab).hom.app X ≫ f) =
      (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).homEquiv X Y f ≫
        (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
          hab.symm)).hom.app Y := by
  have key := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a)
    ((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).ofNatIsoRight
      (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k) hab.symm)))
    (x := X) (y := Y) f
  rw [show (Adjunction.leftAdjointUniq
      (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a)
      ((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).ofNatIsoRight
        (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k) hab.symm)))) =
      _root_.PresheafOfModules.pullbackCongr hab from rfl] at key
  rw [key, Adjunction.homEquiv_ofNatIsoRight_apply]

/-- The reindexing of a pushforward along an equality of maps of presheaves of rings is the
identity on underlying presheaves. -/
public theorem toPresheaf_map_eqToIso_pushforward_hom_app_app {a b : S ⟶ F.op ⋙ R} (hab : a = b)
    (M : _root_.PresheafOfModules.{u} R) (W : Cᵒᵖ) :
    ((_root_.PresheafOfModules.toPresheaf S).map
      ((eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
        hab)).hom.app M)).app W = 𝟙 _ := by
  subst hab
  simp

end Stacks.PresheafOfModules


namespace Stacks.Sites

section PullbackSections

variable {V₀ V₁ : Scheme.{u}}

/-- Four arrows, composed in the two ways the base-change square needs. -/
private theorem comp_four_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₃ ⟶ O₄) (d : O₄ ⟶ O₅)
    (e : O₁ ⟶ O₃) (f : O₁ ⟶ O₄) (hab : a ≫ b = e) (hec : e ≫ c = f) :
    a ≫ b ≫ c ≫ d = f ≫ d := by
  rw [← Category.assoc a b (c ≫ d), ← Category.assoc (a ≫ b) c d, hab, hec]

/-- **A restriction map of the presheaf of Stacks 03DS carries the pullback of a section to the
pullback of that section**, as an equality of maps of sections rather than of their values: the
morphism-level form of `AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`. -/
public theorem pullbackSectionHom_comp_pullbackSectionsMap (F : V₀.Modules) {X Y : Over V₀}
    (g : X ⟶ Y) (V : V₀.Opens) (hY : (⊤ : Y.left.Opens) ≤ Y.hom ⁻¹ᵁ V)
    (hX : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ V) :
    pullbackSectionHom Y.hom F V ⊤ hY ≫ pullbackSectionsMap F g =
      pullbackSectionHom X.hom F V ⊤ hX := by
  ext c
  exact pullbackSectionsMap_pullbackSectionHom F g V hY hX c

/-- **The composition law for pulling global sections back.**  Pulling a global section of `M`
back along `k` and then along `f` is pulling it back along `f ≫ k`, the two readings being
compared by the composition isomorphism `f^*(k^*M) ≅ (f ≫ k)^*M` of the pullback pseudofunctor.
This is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` as an equality of maps of global
sections; it is what the base-change square of the presheaf of Stacks 03DS needs, where neither
side may be read elementwise. -/
public theorem pullbackSectionHom_comp_pullbackSectionHom (M : V₀.Modules) (k : V₁ ⟶ V₀)
    {A : Scheme.{u}} (f : A ⟶ V₁) (hk : (⊤ : V₁.Opens) ≤ k ⁻¹ᵁ (⊤ : V₀.Opens))
    (hf : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : V₁.Opens))
    (hfk : (⊤ : A.Opens) ≤ (f ≫ k) ⁻¹ᵁ (⊤ : V₀.Opens)) :
    pullbackSectionHom k M ⊤ ⊤ hk ≫
        pullbackSectionHom f ((Scheme.Modules.pullback k).obj M) ⊤ ⊤ hf =
      pullbackSectionHom (f ≫ k) M ⊤ ⊤ hfk ≫
        (sectionsTopIso ((Scheme.Modules.pullbackComp f k).app M)).inv := by
  refine (Iso.eq_comp_inv _).mpr ?_
  ext c
  exact Scheme.Modules.pullbackSection_comp f k M ⊤ ⊤ ⊤ hk hf hfk c

/-- **Over the whole space the unit of pullback--pushforward is the pullback of a global
section**, as an equality of maps of global sections:
`AlgebraicGeometry.Scheme.Modules.pullbackSection_top` read morphism-level. -/
public theorem unitTop_eq_pullbackSectionHom (M : V₀.Modules) (k : V₁ ⟶ V₀)
    (hk : (⊤ : V₁.Opens) ≤ k ⁻¹ᵁ (⊤ : V₀.Opens)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M) ⊤ =
      pullbackSectionHom k M ⊤ ⊤ hk := by
  ext c
  exact (Scheme.Modules.pullbackSection_top k M hk c).symm

/-- **Pulling a global section back in one step or in two agrees on the presheaf of Stacks
03DS.**  Let `k : V₁ ⟶ V₀` be a morphism of schemes, let `A₀` and `A₀'` be slice objects whose
structure morphisms contain the open `⊤` in the preimage of the open `⊤`, and let `A ⟶ A₀` and
`A' ⟶ A₀'` be arrows of the two slices.  Pulling a global section of `𝓖` back to `V₁`, then to
`A₀'`, then restricting to `A'` is the same as pulling it back to `A₀`, restricting to `A`,
restricting along an arrow `n` of `Sch/V₀` out of the base change of `A'`, and base changing
along `k`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` read through
`Stacks.Sites.pullbackSectionHom_comp_pullbackSectionsMap` and
`Stacks.Sites.unitTop_eq_pullbackSectionHom`; `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`
is by construction the composition isomorphism of the pullback pseudofunctor on sections, which
is what `Stacks.Sites.pullbackSectionHom_comp_pullbackSectionHom` produces. -/
public theorem pullbackSectionHom_comp_quasiCoherentPresheafBaseChangeIso (𝓖 : V₀.Modules)
    [𝓖.IsQuasicoherent] (k : V₁ ⟶ V₀) {A₀ A : Over V₀} {A₀' A' : Over V₁}
    (g : A ⟶ A₀) (g' : A' ⟶ A₀') (n : (Over.map k).obj A' ⟶ A)
    (h₀ : (⊤ : A₀.left.Opens) ≤ A₀.hom ⁻¹ᵁ (⊤ : V₀.Opens))
    (h₀' : (⊤ : A₀'.left.Opens) ≤ A₀'.hom ⁻¹ᵁ (⊤ : V₁.Opens)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app 𝓖) ⊤ ≫
        pullbackSectionHom A₀'.hom ((Scheme.Modules.pullback k).obj 𝓖) ⊤ ⊤ h₀' ≫
          pullbackSectionsMap ((Scheme.Modules.pullback k).obj 𝓖) g' =
      pullbackSectionHom A₀.hom 𝓖 ⊤ ⊤ h₀ ≫
        pullbackSectionsMap 𝓖 g ≫
          (quasiCoherentPresheafFunctor V₀ 𝓖).map n.op ≫
            (quasiCoherentPresheafBaseChangeIso 𝓖 (Over.mk k)).hom.app (op A') := by
  have hk : (⊤ : V₁.Opens) ≤ k ⁻¹ᵁ (⊤ : V₀.Opens) := by simp
  have hA' : (⊤ : A'.left.Opens) ≤ A'.hom ⁻¹ᵁ (⊤ : V₁.Opens) := by simp
  have hA : (⊤ : A.left.Opens) ≤ A.hom ⁻¹ᵁ (⊤ : V₀.Opens) := by simp
  have h₁ : (⊤ : A'.left.Opens) ≤ (A'.hom ≫ k) ⁻¹ᵁ (⊤ : V₀.Opens) := by simp
  have hrhs := comp_four_algebra (pullbackSectionHom A₀.hom 𝓖 ⊤ ⊤ h₀)
    (pullbackSectionsMap 𝓖 g) (pullbackSectionsMap 𝓖 n)
    (sectionsTopIso ((Scheme.Modules.pullbackComp A'.hom k).app 𝓖)).inv
    (pullbackSectionHom A.hom 𝓖 ⊤ ⊤ hA) (pullbackSectionHom (A'.hom ≫ k) 𝓖 ⊤ ⊤ h₁)
    (pullbackSectionHom_comp_pullbackSectionsMap 𝓖 g ⊤ h₀ hA)
    (pullbackSectionHom_comp_pullbackSectionsMap 𝓖 n ⊤ hA h₁)
  refine Eq.trans ?_ hrhs.symm
  refine Eq.trans (whisker_eq _ (pullbackSectionHom_comp_pullbackSectionsMap
    ((Scheme.Modules.pullback k).obj 𝓖) g' ⊤ h₀' hA')) ?_
  exact Eq.trans (eq_whisker (unitTop_eq_pullbackSectionHom 𝓖 k hk) _)
    (pullbackSectionHom_comp_pullbackSectionHom 𝓖 k A'.hom hk hA' h₁)

end PullbackSections

end Stacks.Sites


namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T) (F : T.Modules)
  [F.IsQuasicoherent]

/-- **The unit of the associated-module adjunction over an open, read through Stacks 070S.** -/
public theorem unitTop_comp_associatedModulePresheafIso (V : T.Opens) :
    Scheme.Modules.Hom.app ((associatedModuleAdjunction E T hT).unit.app F) V ≫
        (associatedModulePresheafIso E T hT F).hom.app (op (opensObj E T hT V)) =
      ((PresheafOfModules.toPresheaf _).map (sectionsUnit E T hT F)).app (op V) := by
  refine Eq.trans ?_ (congrArg (fun t => ((PresheafOfModules.toPresheaf _).map t).app (op V))
    (forget_map_associatedModuleAdjunction_unit_comp_isoSectionsPresheaf E T hT F))
  rfl

/-- The Stacks 070S identification carries the passage from the open `⊤` to the final object to
a restriction map of the presheaf of Stacks 03DS. -/
public theorem restrictModuleSectionsTopIso_hom_comp_associatedModulePresheafIso :
    (restrictModuleSectionsTopIso E T hT ((associatedModule E T hT).obj F)).hom ≫
        (associatedModulePresheafIso E T hT F).hom.app (op (final E T hT)) =
      (associatedModulePresheafIso E T hT F).hom.app (op (opensObj E T hT ⊤)) ≫
        pullbackSectionsMap F ((toOver E T hT).map (finalIsoOpensObjTop E T hT).hom) := by
  rw [restrictModuleSectionsTopIso_hom]
  exact associatedModulePresheafIso_hom_naturality E T hT F (finalIsoOpensObjTop E T hT).hom.op

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {z' z : 𝒳} (ψ : z' ⟶ z)

/-- The category algebra of the base-change compatibility prefix. -/
private theorem glue {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : C}
    {uTrt : O₁ ⟶ O₃} {uT : O₁ ⟶ O₂} {rt : O₂ ⟶ O₃} {uu : O₃ ⟶ O₄} {eb : O₄ ⟶ O₅}
    {tz : O₃ ⟶ O₆} {rf : O₆ ⟶ O₅} {tw : O₂ ⟶ O₇} {rg : O₇ ⟶ O₆}
    {ua : O₁ ⟶ O₈} {u2rt : O₈ ⟶ O₅} {u2 : O₈ ⟶ O₉} {rbc : O₉ ⟶ O₇} {rt' : O₉ ⟶ O₅}
    (hpre : uTrt = uT ≫ rt) (hpost : u2rt = u2 ≫ rt')
    (h1 : uu ≫ eb = tz ≫ rf) (h2 : rt ≫ tz = tw ≫ rg)
    (h3 : uT ≫ tw = ua ≫ u2 ≫ rbc) (h4 : rbc ≫ rg ≫ rf = rt') :
    uTrt ≫ uu ≫ eb = ua ≫ u2rt := by
  rw [hpre, hpost, h1, ← h4]
  simp only [Category.assoc, reassoc_of% h2, reassoc_of% h3]

/-- Three restriction maps, composed. -/
private theorem map_op_comp₃ {C : Type*} [Category C] {D : Type*} [Category D] (F : Cᵒᵖ ⥤ D)
    {W₁ W₂ W₃ W₄ : C} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) (k : W₃ ⟶ W₄) :
    F.map k.op ≫ F.map g.op ≫ F.map f.op = F.map (f ≫ g ≫ k).op := by
  simp

/-- Appending a morphism which is an identity. -/
private theorem comp_eq_of_id {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) : f ≫ g = f := by rw [hg, Category.comp_id]

/-- The three factors of `associatedModuleObjSmallEtaleBaseChangeIso`. -/
theorem associatedModuleObjSmallEtaleBaseChangeIso_hom_factors
    (𝓖 : (p.obj z).left.1.Modules) :
    (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ 𝓖).hom =
      (PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj) (𝟙 _)).map
          ((smallEtalePullbackComparisonIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ).hom.app
            ((SmallEtale.associatedModule E (p.obj z).left.1
              (contains_base B E h S hS p z)).obj 𝓖).val) ≫
        ((SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
            (smallEtaleBaseMorphism B E h S hS p ψ))).inv.app
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj 𝓖) ≫
        (SmallEtale.associatedModuleBaseChangeIso E
          (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖) := rfl

/-- `smallEtalePullbackComparisonIso` is `PresheafOfModules.pullbackCongr`. -/
theorem smallEtalePullbackComparisonIso_eq :
    smallEtalePullbackComparisonIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ =
      PresheafOfModules.pullbackCongr.{u}
        (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
          (etaleTopology B) (etaleTopology_le_topology B) ψ) := rfl

section Abbrevs

/-- The structure sheaf of the small étale site of the scheme below `y`. -/
private noncomputable abbrev strSheaf (y : 𝒳) :=
  SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)

/-- The associated-module functor of the small étale site of the scheme below `y`. -/
private noncomputable abbrev assocMod (y : 𝒳) :=
  SmallEtale.associatedModule E (p.obj y).left.1 (contains_base B E h S hS p y)

/-- The morphism of schemes below an arrow of `𝒳`, as a morphism of the big étale site. -/
private abbrev belowEtale (ψ : z' ⟶ z) := smallEtaleBaseMorphism B E h S hS p ψ

/-- The passage from sheaves to presheaves of modules on the small étale site below `y`. -/
private noncomputable abbrev forgetRS (y : 𝒳) :=
  SheafOfModules.forget (strSheaf B E h S hS p y) ⋙
    PresheafOfModules.restrictScalars (𝟙 (strSheaf B E h S hS p y).obj)

/-- The identification of Stacks 03LC (1) at `𝓖`, read backwards. -/
private noncomputable abbrev bcInvApp (ψ : z' ⟶ z) (𝓖 : (p.obj z).left.1.Modules) :=
  (SmallEtale.associatedModuleBaseChangeIso E (belowEtale B E h S hS p ψ)).inv.app 𝓖

/-- The transpose of `AlgebraicGeometry.Stack.bcInvApp` across the adjunction along `ε_ψ`. -/
private noncomputable abbrev bigT (ψ : z' ⟶ z) (𝓖 : (p.obj z).left.1.Modules) :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E (belowEtale B E h S hS p ψ))).homEquiv
    ((assocMod B E h S hS p z).obj 𝓖)
    ((assocMod B E h S hS p z').obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))
    (bcInvApp B E h S hS p ψ 𝓖)

/-- The underlying map of presheaves of `AlgebraicGeometry.Stack.bigT`. -/
private noncomputable abbrev bigTp (ψ : z' ⟶ z) (𝓖 : (p.obj z).left.1.Modules) :=
  (PresheafOfModules.toPresheaf (strSheaf B E h S hS p z).obj).map
    ((SheafOfModules.forget (strSheaf B E h S hS p z)).map (bigT B E h S hS p ψ 𝓖))

end Abbrevs

/-- `PresheafOfModules.toPresheaf` splits composites on sections. -/
theorem toPresheaf_map_comp_app {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P) (W : Cᵒᵖ) :
    ((PresheafOfModules.toPresheaf R).map (f ≫ g)).app W =
      ((PresheafOfModules.toPresheaf R).map f).app W ≫
        ((PresheafOfModules.toPresheaf R).map g).app W := rfl

/-- **The sheafification transpose of the base-change identification.**  The identification
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` begins with the
sheafification of the comparison of the two spellings of the pullback of presheaves of modules,
which `CategoryTheory.Adjunction.homEquiv_naturality_left` moves outside the transpose. -/
theorem homEquiv_sheafification_bcIso (𝓖 : (p.obj z).left.1.Modules) :
    (PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj)).homEquiv
        ((PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
            (etaleTopology_le_topology B))).obj
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj 𝓖).val)
        ((SmallEtale.associatedModule E (p.obj z').left.1
          (contains_base B E h S hS p z')).obj
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ 𝓖).hom =
      (smallEtalePullbackComparisonIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ).hom.app
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj 𝓖).val ≫
        ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                (contains_base B E h S hS p z')).obj)).unit.app
            ((PresheafOfModules.pullback.{u}
              (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ)).hom).obj
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖).val) ≫
          (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj)).map
            ((SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ))).inv.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖) ≫
            (SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖)) := by
  rw [associatedModuleObjSmallEtaleBaseChangeIso_hom_factors]
  refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _) ?_
  refine whisker_eq _ ?_
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
      (contains_base B E h S hS p z')).obj)).homEquiv_unit _ _ _

/-- **The transpose of the Stacks 03LC (1) identification.**  The adjunct, along the
pullback--pushforward adjunction of presheaves of modules at the map `ψ_{small}^♯` of
**Stacks 06WC**, of the sheafification-adjunct of
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` is the adjunct along the
adjunction of *sheaves* of modules of the inverse of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, read on underlying presheaves and
reindexed along
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`. -/
theorem homEquiv_pullback_bcIso (𝓖 : (p.obj z).left.1.Modules) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
            (etaleTopology_le_topology B))).homEquiv
        ((SmallEtale.associatedModule E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj 𝓖).val
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj)).obj
          ((SmallEtale.associatedModule E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)))
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj)).homEquiv _ _
          (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ 𝓖).hom) =
      (SheafOfModules.forget _).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (SmallEtale.smallEtaleStructureMapRing E
              (smallEtaleBaseMorphism B E h S hS p ψ))).homEquiv
            ((SmallEtale.associatedModule E (p.obj z).left.1
              (contains_base B E h S hS p z)).obj 𝓖)
            ((SmallEtale.associatedModule E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))
            ((SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖)) ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
            (etaleTopology B) (etaleTopology_le_topology B) ψ).symm)).hom.app _ := by
  rw [homEquiv_sheafification_bcIso, smallEtalePullbackComparisonIso_eq]
  refine Eq.trans (Stacks.PresheafOfModules.homEquiv_pullbackCongr_hom_app_comp
    (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) ψ) _ _ _) ?_
  refine eq_whisker ?_ _
  exact SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app
    (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p ψ))
    ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj 𝓖)
    ((SmallEtale.associatedModule E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))
    ((SmallEtale.associatedModuleBaseChangeIso E
      (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖)

/-- `AlgebraicGeometry.Stack.finalToBaseChangeFinal` is the canonical arrow out of the final
object into the base change of the final object. -/
private theorem finalToBaseChangeFinal_eq :
    finalToBaseChangeFinal B E h S hS p ψ =
      (smallEtaleBaseChange_finalIsTerminal E (belowEtale B E h S hS p ψ)).from
        (SmallEtale.final E (p.obj z').left.1 (contains_base B E h S hS p z')) := rfl

section Assembly

variable (𝓖 : (p.obj z).left.1.Modules)

/-- The invertible prefix at `y`: the unit of the associated-module adjunction over `⊤`,
followed by the identification of the sections of a restriction over `⊤` with the sections over
the final object. -/
private noncomputable def unitFinalPrefix (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules) :
    ((SheafOfModules.forget ((p.obj y).left.1).ringCatSheaf).obj 𝓕).presheaf.obj
        (op (⊤ : (p.obj y).left.1.Opens)) ⟶
      ((assocMod B E h S hS p y).obj 𝓕).val.presheaf.obj
        (op (smallEtaleFinal B E h S hS p y)) :=
  Scheme.Modules.Hom.app ((SmallEtale.associatedModuleAdjunction E (p.obj y).left.1
      (contains_base B E h S hS p y)).unit.app 𝓕) ⊤ ≫
    (SmallEtale.restrictModuleSectionsTopIso E (p.obj y).left.1
      (contains_base B E h S hS p y) ((assocMod B E h S hS p y).obj 𝓕)).hom

/-- The invertible prefix, written out. -/
private theorem unitFinalPrefix_eq (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules) :
    unitFinalPrefix B E h S hS p y 𝓕 =
      Scheme.Modules.Hom.app ((SmallEtale.associatedModuleAdjunction E (p.obj y).left.1
          (contains_base B E h S hS p y)).unit.app 𝓕) ⊤ ≫
        (SmallEtale.restrictModuleSectionsTopIso E (p.obj y).left.1
          (contains_base B E h S hS p y) ((assocMod B E h S hS p y).obj 𝓕)).hom := rfl

/-- The invertible prefix at `z'`, with its first factor pushed forward along the morphism of
schemes below `ψ`: the pushforward does not move global sections. -/
private theorem unitFinalPrefix_pushforward (𝓖 : (p.obj z).left.1.Modules) :
    unitFinalPrefix B E h S hS p z'
        ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pushforward
            (B.inclusion.map (p.map ψ).left)).map
          ((SmallEtale.associatedModuleAdjunction E (p.obj z').left.1
            (contains_base B E h S hS p z')).unit.app
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))) ⊤ ≫
        (SmallEtale.restrictModuleSectionsTopIso E (p.obj z').left.1
          (contains_base B E h S hS p z')
          ((assocMod B E h S hS p z').obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))).hom := rfl


/-- Pulling a global section back to the open subscheme `⊤`, with its target read as the value
of the presheaf of Stacks 03DS. -/
private noncomputable def sectionsUnitTop (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules)
    [𝓕.IsQuasicoherent] :
    𝓕.val.presheaf.obj (op (⊤ : (p.obj y).left.1.Opens)) ⟶
      ((SmallEtale.toOver E (p.obj y).left.1 (contains_base B E h S hS p y)).op ⋙
        quasiCoherentPresheafFunctor (p.obj y).left.1 𝓕).obj
        (op (SmallEtale.opensObj E (p.obj y).left.1 (contains_base B E h S hS p y) ⊤)) :=
  ((PresheafOfModules.toPresheaf _).map (SmallEtale.sectionsUnit E (p.obj y).left.1
    (contains_base B E h S hS p y) 𝓕)).app (op (⊤ : (p.obj y).left.1.Opens))

/-- `AlgebraicGeometry.Stack.sectionsUnitTop` is the transpose of the Stacks 070S
identification over the open `⊤`. -/
private theorem unitTop_comp_apO (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules) [𝓕.IsQuasicoherent] :
    Scheme.Modules.Hom.app ((SmallEtale.associatedModuleAdjunction E (p.obj y).left.1
          (contains_base B E h S hS p y)).unit.app 𝓕) ⊤ ≫
        (SmallEtale.associatedModulePresheafIso E (p.obj y).left.1
          (contains_base B E h S hS p y) 𝓕).hom.app
          (op (SmallEtale.opensObj E (p.obj y).left.1 (contains_base B E h S hS p y) ⊤)) =
      sectionsUnitTop B E h S hS p y 𝓕 :=
  SmallEtale.unitTop_comp_associatedModulePresheafIso E (p.obj y).left.1
    (contains_base B E h S hS p y) 𝓕 ⊤

/-- The inverse of `AlgebraicGeometry.Stack.sectionsUnitTop`, on the left. -/
private theorem inv_comp_sectionsUnitTop (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules)
    [𝓕.IsQuasicoherent]
    (isu : IsIso (SmallEtale.sectionsUnit E (p.obj y).left.1
      (contains_base B E h S hS p y) 𝓕)) :
    ((PresheafOfModules.toPresheaf _).map (@CategoryTheory.inv _ _ _ _ _ isu)).app
        (op (⊤ : (p.obj y).left.1.Opens)) ≫ sectionsUnitTop B E h S hS p y 𝓕 = 𝟙 _ := by
  show ((PresheafOfModules.toPresheaf _).map (@CategoryTheory.inv _ _ _ _ _ isu)).app
        (op (⊤ : (p.obj y).left.1.Opens)) ≫
      ((PresheafOfModules.toPresheaf _).map (SmallEtale.sectionsUnit E (p.obj y).left.1
        (contains_base B E h S hS p y) 𝓕)).app (op (⊤ : (p.obj y).left.1.Opens)) = 𝟙 _
  rw [← toPresheaf_map_comp_app, @IsIso.inv_hom_id _ _ _ _ _ isu,
    CategoryTheory.Functor.map_id, NatTrans.id_app]

/-- **The invertible prefix may be cancelled.** -/
private theorem eq_of_unitFinalPrefix_comp_eq (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules)
    [𝓕.IsQuasicoherent] {X : AddCommGrpCat.{u}}
    {L R : ((assocMod B E h S hS p y).obj 𝓕).val.presheaf.obj
      (op (smallEtaleFinal B E h S hS p y)) ⟶ X}
    (hw : unitFinalPrefix B E h S hS p y 𝓕 ≫ L =
      unitFinalPrefix B E h S hS p y 𝓕 ≫ R) : L = R := by
  have isu := SmallEtale.isIso_sectionsUnit E (p.obj y).left.1
    (contains_base B E h S hS p y) 𝓕
  exact Stacks.CategoryTheory.eq_of_split_prefix_comp_eq
    (SmallEtale.restrictModuleSectionsTopIso E (p.obj y).left.1
      (contains_base B E h S hS p y) ((assocMod B E h S hS p y).obj 𝓕)).inv
    (sectionsUnitTop B E h S hS p y 𝓕)
    (((PresheafOfModules.toPresheaf _).map (@CategoryTheory.inv _ _ _ _ _ isu)).app
      (op (⊤ : (p.obj y).left.1.Opens)))
    ((SmallEtale.associatedModulePresheafIso E (p.obj y).left.1
      (contains_base B E h S hS p y) 𝓕).hom.app
      (op (SmallEtale.opensObj E (p.obj y).left.1 (contains_base B E h S hS p y) ⊤)))
    ((SmallEtale.associatedModulePresheafIso E (p.obj y).left.1
      (contains_base B E h S hS p y) 𝓕).inv.app
      (op (SmallEtale.opensObj E (p.obj y).left.1 (contains_base B E h S hS p y) ⊤)))
    (unitFinalPrefix_eq B E h S hS p y 𝓕)
    (SmallEtale.restrictModuleSectionsTopIso E (p.obj y).left.1
      (contains_base B E h S hS p y) ((assocMod B E h S hS p y).obj 𝓕)).inv_hom_id
    (inv_comp_sectionsUnitTop B E h S hS p y 𝓕 isu) (Iso.hom_inv_id_app _ _)
    (unitTop_comp_apO B E h S hS p y 𝓕) hw

/-- `h1`: factors 3 and 4 of the base-change identification, read at the final object. -/
private theorem h1_finalPullbackUnit :
    smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ ((assocMod B E h S hS p z).obj 𝓖).val ≫
        (((PresheafOfModules.toPresheaf _).map
              ((PresheafOfModules.sheafificationAdjunction
                    (𝟙 (strSheaf B E h S hS p z').obj)).unit.app
                ((PresheafOfModules.pullback.{u}
                  (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                    (etaleTopology_le_topology B))).obj
                  ((assocMod B E h S hS p z).obj 𝓖).val))).app
              (op (smallEtaleFinal B E h S hS p z')) ≫
            ((PresheafOfModules.toPresheaf _).map
                ((forgetRS B E h S hS p z').map
                  (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
                    (etaleTopology_le_topology B) ψ 𝓖).hom)).app
              (op (smallEtaleFinal B E h S hS p z'))) =
      (show ((assocMod B E h S hS p z).obj 𝓖).val.presheaf.obj
            (op (smallEtaleFinal B E h S hS p z)) ⟶
          ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.obj
            (op ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).obj
              (smallEtaleFinal B E h S hS p z))) from
          (bigTp B E h S hS p ψ 𝓖).app (op (smallEtaleFinal B E h S hS p z))) ≫
        ((assocMod B E h S hS p z').obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
              𝓖)).val.presheaf.map (finalToBaseChangeFinal B E h S hS p ψ).op := by
  have eqA := smallEtaleFinalPullbackUnit_comp B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) ψ ((assocMod B E h S hS p z).obj 𝓖).val
    ((assocMod B E h S hS p z).obj 𝓖).val
    ((forgetRS B E h S hS p z').obj
      ((assocMod B E h S hS p z').obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)))
    (𝟙 _)
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (strSheaf B E h S hS p z').obj)).homEquiv _ _
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ 𝓖).hom)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, NatTrans.id_app] at eqA
  refine Eq.trans ?_ (Eq.trans eqA ?_)
  · exact whisker_eq _ (toPresheaf_map_comp_app _ _ _).symm
  · refine eq_whisker ?_ _
    refine Eq.trans (congrArg (fun t => ((PresheafOfModules.toPresheaf _).map t).app _)
      (homEquiv_pullback_bcIso B E h S hS p hp ψ 𝓖)) ?_
    exact Eq.trans (toPresheaf_map_comp_app _ _ _)
      (comp_eq_of_id _ _
        (Stacks.PresheafOfModules.toPresheaf_map_eqToIso_pushforward_hom_app_app
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
            (etaleTopology B) (etaleTopology_le_topology B) ψ).symm _ _))

/-- `h2`: naturality of the transpose between the two final objects. -/
private theorem h2_naturality :
    (SmallEtale.restrictModuleSectionsTopIso E (p.obj z).left.1
          (contains_base B E h S hS p z) ((assocMod B E h S hS p z).obj 𝓖)).hom ≫
        (show ((assocMod B E h S hS p z).obj 𝓖).val.presheaf.obj
              (op (smallEtaleFinal B E h S hS p z)) ⟶
            ((assocMod B E h S hS p z').obj
                ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                  𝓖)).val.presheaf.obj
              (op ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).obj
                (smallEtaleFinal B E h S hS p z))) from
            (bigTp B E h S hS p ψ 𝓖).app (op (smallEtaleFinal B E h S hS p z))) =
      (show ((assocMod B E h S hS p z).obj 𝓖).val.presheaf.obj
            (op (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤)) ⟶
          ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.obj
            (op ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).obj
              (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤))) from
          (bigTp B E h S hS p ψ 𝓖).app
            (op (SmallEtale.opensObj E (p.obj z).left.1
              (contains_base B E h S hS p z) ⊤))) ≫
        ((assocMod B E h S hS p z').obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
              𝓖)).val.presheaf.map
          ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).map
            (SmallEtale.finalIsoOpensObjTop E (p.obj z).left.1
              (contains_base B E h S hS p z)).hom).op := by
  rw [SmallEtale.restrictModuleSectionsTopIso_hom]
  exact (bigTp B E h S hS p ψ 𝓖).naturality
    (SmallEtale.finalIsoOpensObjTop E (p.obj z).left.1
      (contains_base B E h S hS p z)).hom.op

/-- `h4`: the three restriction maps collapse to the identification at `z'`. -/
private theorem h4_restrictions :
    ((assocMod B E h S hS p z').obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
              𝓖)).val.presheaf.map
          ((SmallEtale.baseChangeOpensIso E (belowEtale B E h S hS p ψ)).inv.app ⊤).op ≫
        ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.map
            ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).map
              (SmallEtale.finalIsoOpensObjTop E (p.obj z).left.1
                (contains_base B E h S hS p z)).hom).op ≫
          ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.map (finalToBaseChangeFinal B E h S hS p ψ).op =
      (SmallEtale.restrictModuleSectionsTopIso E (p.obj z').left.1
        (contains_base B E h S hS p z')
        ((assocMod B E h S hS p z').obj
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))).hom := by
  rw [SmallEtale.restrictModuleSectionsTopIso_hom, finalToBaseChangeFinal_eq]
  refine Eq.trans (map_op_comp₃ _ _ _ _) ?_
  exact congrArg (fun r => ((assocMod B E h S hS p z').obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
        𝓖)).val.presheaf.map (Quiver.Hom.op r))
    (SmallEtale.finalToBaseChangeFinal_comp_baseChangeOpensIso_inv_app_top E
      (belowEtale B E h S hS p ψ))

/-- The two halves of the Stacks 03LC (1) transpose, merged on sections over `⊤`. -/
private theorem restrictModule_map_bigT_app_top :
    Scheme.Modules.Hom.app ((SmallEtale.restrictModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (SmallEtale.smallEtaleStructureMapRing E (belowEtale B E h S hS p ψ))).unit.app
            ((assocMod B E h S hS p z).obj 𝓖))) ⊤ ≫
        Scheme.Modules.Hom.app ((SmallEtale.restrictModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).map
          ((SheafOfModules.pushforward.{u}
            (SmallEtale.smallEtaleStructureMapRing E (belowEtale B E h S hS p ψ))).map
            (bcInvApp B E h S hS p ψ 𝓖))) ⊤ =
      (show ((assocMod B E h S hS p z).obj 𝓖).val.presheaf.obj
            (op (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤)) ⟶
          ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.obj
            (op ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).obj
              (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤))) from
          (bigTp B E h S hS p ψ 𝓖).app
            (op (SmallEtale.opensObj E (p.obj z).left.1
              (contains_base B E h S hS p z) ⊤))) := by
  refine Eq.trans (Scheme.Modules.Hom.comp_app _ _).symm ?_
  refine Eq.trans (congrArg (fun t => Scheme.Modules.Hom.app t ⊤)
    (CategoryTheory.Functor.map_comp (SmallEtale.restrictModule E (p.obj z).left.1
      (contains_base B E h S hS p z)) _ _).symm) ?_
  exact congrArg (fun t => Scheme.Modules.Hom.app
    ((SmallEtale.restrictModule E (p.obj z).left.1 (contains_base B E h S hS p z)).map t) ⊤)
    (Adjunction.homEquiv_unit _ _ _ _).symm

/-- `h3`: the Stacks 03LC (1) conjugacy, with the two restrictions merged. -/
private theorem h3_bridge :
    Scheme.Modules.Hom.app ((SmallEtale.associatedModuleAdjunction E (p.obj z).left.1
          (contains_base B E h S hS p z)).unit.app 𝓖) ⊤ ≫
        (show ((assocMod B E h S hS p z).obj 𝓖).val.presheaf.obj
              (op (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤)) ⟶
            ((assocMod B E h S hS p z').obj
                ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                  𝓖)).val.presheaf.obj
              (op ((smallEtaleBaseChange E (belowEtale B E h S hS p ψ)).obj
                (SmallEtale.opensObj E (p.obj z).left.1 (contains_base B E h S hS p z) ⊤))) from
            (bigTp B E h S hS p ψ 𝓖).app
              (op (SmallEtale.opensObj E (p.obj z).left.1
                (contains_base B E h S hS p z) ⊤))) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
            (B.inclusion.map (p.map ψ).left)).unit.app 𝓖) ⊤ ≫
        Scheme.Modules.Hom.app ((Scheme.Modules.pushforward
              (B.inclusion.map (p.map ψ).left)).map
            ((SmallEtale.associatedModuleAdjunction E (p.obj z').left.1
              (contains_base B E h S hS p z')).unit.app
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖))) ⊤ ≫
          ((assocMod B E h S hS p z').obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
                𝓖)).val.presheaf.map
            ((SmallEtale.baseChangeOpensIso E
              (belowEtale B E h S hS p ψ)).inv.app ⊤).op := by
  have key := SmallEtale.associatedModuleBaseChangeIso_inv_unit_sections_top E
    (belowEtale B E h S hS p ψ) 𝓖
  rw [Category.assoc] at key
  refine Eq.trans ?_ key.symm
  exact whisker_eq _ (restrictModule_map_bigT_app_top B E h S hS p ψ 𝓖).symm


/-- **Lemma A.**  The invertible prefix at `z` carries factors 3 and 4 of the base-change
identification to the invertible prefix at `z'`. -/
private theorem unitFinal_comp_bcIso :
    unitFinalPrefix B E h S hS p z 𝓖 ≫
        smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ ((assocMod B E h S hS p z).obj 𝓖).val ≫
          (((PresheafOfModules.toPresheaf _).map
                ((PresheafOfModules.sheafificationAdjunction
                      (𝟙 (strSheaf B E h S hS p z').obj)).unit.app
                  ((PresheafOfModules.pullback.{u}
                    (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                      (etaleTopology_le_topology B))).obj
                    ((assocMod B E h S hS p z).obj 𝓖).val))).app
                (op (smallEtaleFinal B E h S hS p z')) ≫
              ((PresheafOfModules.toPresheaf _).map
                  ((forgetRS B E h S hS p z').map
                    (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
                      (etaleTopology_le_topology B) ψ 𝓖).hom)).app
                (op (smallEtaleFinal B E h S hS p z'))) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
          (B.inclusion.map (p.map ψ).left)).unit.app 𝓖) ⊤ ≫
        unitFinalPrefix B E h S hS p z'
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖) :=
  glue (unitFinalPrefix_eq B E h S hS p z 𝓖)
    (unitFinalPrefix_pushforward B E h S hS p ψ 𝓖)
    (h1_finalPullbackUnit B E h S hS p hp ψ 𝓖)
    (h2_naturality B E h S hS p ψ 𝓖) (h3_bridge B E h S hS p ψ 𝓖)
    (h4_restrictions B E h S hS p ψ 𝓖)


/-- The category algebra of the invertible prefix against the Stacks 070S identification. -/
private theorem prefix_apO_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    {pf : O₁ ⟶ O₃} {a : O₁ ⟶ O₂} {r : O₂ ⟶ O₃} {apO : O₃ ⟶ O₄} {ap : O₂ ⟶ O₅}
    {pm : O₅ ⟶ O₄} {s : O₁ ⟶ O₅}
    (hpre : pf = a ≫ r) (h1 : r ≫ apO = ap ≫ pm) (h2 : a ≫ ap = s) :
    pf ≫ apO = s ≫ pm := by
  rw [hpre, Category.assoc, h1, ← Category.assoc, h2]

/-- **The invertible prefix against the Stacks 070S identification at the final object.**  The
prefix at `y`, followed by the Stacks 070S identification of the sections of `𝓕^a` over the
final object with those of the presheaf of Stacks 03DS, is
`AlgebraicGeometry.Stack.sectionsUnitTop` followed by the restriction map of that presheaf along
`AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop`. -/
private theorem unitFinalPrefix_comp_apO (y : 𝒳) (𝓕 : (p.obj y).left.1.Modules)
    [𝓕.IsQuasicoherent] :
    unitFinalPrefix B E h S hS p y 𝓕 ≫
        (SmallEtale.associatedModulePresheafIso E (p.obj y).left.1
            (contains_base B E h S hS p y) 𝓕).hom.app
          (op (smallEtaleFinal B E h S hS p y)) =
      sectionsUnitTop B E h S hS p y 𝓕 ≫
        pullbackSectionsMap 𝓕 ((SmallEtale.toOver E (p.obj y).left.1
            (contains_base B E h S hS p y)).map
          (SmallEtale.finalIsoOpensObjTop E (p.obj y).left.1
            (contains_base B E h S hS p y)).hom) :=
  prefix_apO_algebra (unitFinalPrefix_eq B E h S hS p y 𝓕)
    (SmallEtale.restrictModuleSectionsTopIso_hom_comp_associatedModulePresheafIso E
      (p.obj y).left.1 (contains_base B E h S hS p y) 𝓕)
    (unitTop_comp_apO B E h S hS p y 𝓕)

/-- **Lemma B.  The Stacks 03DS side of the carried compatibility.**  Pulling a global section
of `𝓖` back to the final object of the small étale site of the scheme below `z'` in one step --
along the morphism of schemes below `ψ` and then down -- or in two -- down to the final object
below `z`, along the arrow `n` of `Sch/W` below `ψ`, and then base changing -- agree.

This is `Stacks.Sites.pullbackSectionHom_comp_quasiCoherentPresheafBaseChangeIso` at the two
final objects, read through their identification with the opens `⊤` by
`AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop`:
`AlgebraicGeometry.Stack.sectionsUnitTop` is by construction the map
`AlgebraicGeometry.pullbackSectionHom` along the inclusion of the open `⊤`, which is the
structure morphism of `AlgebraicGeometry.SmallEtale.opensObj` at `⊤`. -/
private theorem step3_pullbackSections (𝓖 : (p.obj z).left.1.Modules) [𝓖.IsQuasicoherent]
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
          (B.inclusion.map (p.map ψ).left)).unit.app 𝓖) ⊤ ≫
        sectionsUnitTop B E h S hS p z'
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖) ≫
          pullbackSectionsMap
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)
            ((SmallEtale.toOver E (p.obj z').left.1
                (contains_base B E h S hS p z')).map
              (SmallEtale.finalIsoOpensObjTop E (p.obj z').left.1
                (contains_base B E h S hS p z')).hom) =
      sectionsUnitTop B E h S hS p z 𝓖 ≫
        pullbackSectionsMap 𝓖
            ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).map
              (SmallEtale.finalIsoOpensObjTop E (p.obj z).left.1
                (contains_base B E h S hS p z)).hom) ≫
          (quasiCoherentPresheafFunctor (p.obj z).left.1 𝓖).map n.op ≫
            (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
                (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
              (op ((SmallEtale.toOver E (p.obj z').left.1
                (contains_base B E h S hS p z')).obj
                (smallEtaleFinal B E h S hS p z'))) :=
  Stacks.Sites.pullbackSectionHom_comp_quasiCoherentPresheafBaseChangeIso 𝓖
    (B.inclusion.map (p.map ψ).left)
    ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).map
      (SmallEtale.finalIsoOpensObjTop E (p.obj z).left.1
        (contains_base B E h S hS p z)).hom)
    ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).map
      (SmallEtale.finalIsoOpensObjTop E (p.obj z').left.1
        (contains_base B E h S hS p z')).hom)
    n (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage le_rfl)

/-- The category algebra which glues Lemma A, Lemma B and the invertible prefix. -/
private theorem compat_algebra {C : Type*} [Category C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : C}
    {pf : O₁ ⟶ O₂} {m1 : O₂ ⟶ O₃} {m2 : O₃ ⟶ O₄} {m3 : O₄ ⟶ O₅} {apO' : O₅ ⟶ O₆}
    {uu : O₁ ⟶ O₇} {pf' : O₇ ⟶ O₅} {s' : O₇ ⟶ O₈} {pm' : O₈ ⟶ O₆}
    {apO : O₂ ⟶ O₉} {rest : O₉ ⟶ O₆} {s : O₁ ⟶ O₁₀} {pm : O₁₀ ⟶ O₉}
    (hA : pf ≫ m1 ≫ m2 ≫ m3 = uu ≫ pf') (hpf' : pf' ≫ apO' = s' ≫ pm')
    (hpf : pf ≫ apO = s ≫ pm) (hstep : uu ≫ s' ≫ pm' = s ≫ pm ≫ rest) :
    pf ≫ m1 ≫ m2 ≫ m3 ≫ apO' = pf ≫ apO ≫ rest := by
  rw [reassoc_of% hA, hpf', hstep, reassoc_of% hpf]

end Assembly

/-- **The carried base-change compatibility on sections over the final object, proved.**  The
stand-in `AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsFactorFourReduction.lean` is
no longer carried: both sides acquire the invertible prefix
`AlgebraicGeometry.Stack.unitFinalPrefix`, which
`AlgebraicGeometry.Stack.eq_of_unitFinalPrefix_comp_eq` cancels; with the prefix in place the
Stacks 03LC (1) side is `AlgebraicGeometry.Stack.unitFinal_comp_bcIso` and the Stacks 03DS side
is `AlgebraicGeometry.Stack.step3_pullbackSections`, the two being tied to
`AlgebraicGeometry.Stack.sectionsUnitTop` by
`AlgebraicGeometry.Stack.unitFinalPrefix_comp_apO`. -/
theorem associatedModuleBaseChangeFinalSectionsCompat :
    AssociatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp := by
  intro z₁ z₀ χ 𝓖 h𝓖 n _hn
  let := h𝓖
  exact eq_of_unitFinalPrefix_comp_eq B E h S hS p z₀ 𝓖 <|
    compat_algebra (unitFinal_comp_bcIso B E h S hS p hp χ 𝓖)
      (unitFinalPrefix_comp_apO B E h S hS p z₁
        ((Scheme.Modules.pullback (B.inclusion.map (p.map χ).left)).obj 𝓖))
      (unitFinalPrefix_comp_apO B E h S hS p z₀ 𝓖)
      (step3_pullbackSections B E h S hS p χ 𝓖 n)

end AlgebraicGeometry.Stack

end
