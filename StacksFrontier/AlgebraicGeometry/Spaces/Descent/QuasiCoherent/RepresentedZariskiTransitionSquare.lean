module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback

/-!
# The transitions of a descent datum of a represented family under pullback: the square

Let `D` be a descent datum for quasi-coherent modules relative to a family of *representable*
algebraic spaces, and read its pairwise isomorphisms on the underlying schemes,
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn`. **Reading at a pair `(a, b)`
of morphisms of the site and then pulling back along a third morphism `h` is reading at the
composed pair `(h ≫ a, h ≫ b)`**, the two sides compared by the contraction
`AlgebraicGeometry.Scheme.Modules.pullbackComp` of the two pullbacks of modules on the schemes.
This is `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` for
`AlgebraicGeometry.modulePullbackPseudofunctor` at the readings.

## Main results

* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_iso` and
  `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_naturality_iso`: the composition
  law of the comparison `r^*(F|_{Zar}) ≅ (φ^*F)|_{Zar}` and its naturality in the module, as
  equalities of **isomorphisms**.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.restrictModule_transitionOn_representedPairLift_comp_iso`: the same for the restriction of
  the reading of a transition pulled back along a further morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_pullbackComp_iso`: **the
  square**, and `…zariskiTransitionOn_pullbackComp`: the same read on the underlying morphisms.
* `Stacks.iso_square_paste`: the pasting of three commuting squares of isomorphisms with a
  fourth read backwards, at abstract objects.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks

section Paste

variable {C₀ : Type*} [Category C₀]

/-- **The pasting of three commuting squares of isomorphisms with a fourth read backwards.** -/
public theorem iso_square_paste {o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : C₀}
    (A : o1 ≅ o2) (Bm : o2 ≅ o3) (Cc : o4 ≅ o3) (Hpa : o2 ≅ o5) (Hpb : o3 ≅ o6)
    (Ps : o5 ≅ o6) (La : o5 ≅ o7) (Lb : o6 ≅ o8) (Th : o7 ≅ o8)
    (Pa : o1 ≅ o9) (Ra : o9 ≅ o7) (Pb : o4 ≅ o10) (Rb : o10 ≅ o8)
    (i1 : A ≪≫ Hpa ≪≫ La = Pa ≪≫ Ra) (i2 : Bm ≪≫ Hpb = Hpa ≪≫ Ps)
    (i3 : Ps ≪≫ Lb = La ≪≫ Th) (i4 : Cc ≪≫ Hpb ≪≫ Lb = Pb ≪≫ Rb) :
    (A ≪≫ Bm ≪≫ Cc.symm) ≪≫ Pb = Pa ≪≫ Ra ≪≫ Th ≪≫ Rb.symm := by
  have e1 := congrArg Iso.hom i1
  have e2 := congrArg Iso.hom i2
  have e3 := congrArg Iso.hom i3
  have e4 := congrArg Iso.hom i4
  simp only [Iso.trans_hom] at e1 e2 e3 e4
  have e4' : Pb.hom = Cc.hom ≫ Hpb.hom ≫ Lb.hom ≫ Rb.inv := by
    rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv, Category.assoc]
    exact e4.symm
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, e4', Iso.inv_hom_id_assoc]
  rw [reassoc_of% e2, reassoc_of% e3, ← reassoc_of% e1]

end Paste

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Naturality

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_naturality` as an equality of
isomorphisms. -/
public theorem representedZariskiModulePullbackIso_naturality_iso
    {F F' : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (ψ : F ≅ F') :
    (Scheme.Modules.pullback
          (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).mapIso
          ((SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso ψ)) ≪≫
        representedZariskiModulePullbackIso B S hS g hg F' hF' =
      representedZariskiModulePullbackIso B S hS g hg F hF ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
            ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso ψ)) := by
  refine Iso.ext ?_
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using
    representedZariskiModulePullbackIso_naturality B S hS g hg hF hF' ψ.hom

end Naturality

section CompIso

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp` as an equality of
isomorphisms. -/
public theorem representedZariskiModulePullbackIso_comp_iso
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback
          (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).mapIso
          (representedZariskiModulePullbackIso B S hS g hg F hF) ≪≫
        representedZariskiModulePullbackIso B S hS h hh
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
            (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g hg F hF) ≪≫
          (SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).mapIso
            ((representedSmallEtaleModuleEquivalence B S hS T'').inverse.mapIso
              ((representedModulePullbackCompIso B S hS h g).app F)) =
      (Scheme.Modules.pullbackComp
            (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).app
          (representedZariskiModule B S hS T F) ≪≫
        representedZariskiModulePullbackIso B S hS (h ≫ g) hhg F hF := by
  refine Iso.ext ?_
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    representedZariskiModulePullbackIso_comp B S hS h g hh hg hhg F hF

end CompIso

namespace QuasiCoherentDescent

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)
variable (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))
variable {Y Y' : BigFppfOver B S hS} (h : Y' ⟶ Y) {q : Y ⟶ U} {i j : I}
  (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q)
  {q' : Y' ⟶ U} (ha' : (h ≫ a) ≫ f i = q') (hb' : (h ≫ b) ≫ f j = q')

section Coherence

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent`
`.restrictModule_transitionOn_representedPairLift_comp_hom` as an equality of isomorphisms. -/
public theorem restrictModule_transitionOn_representedPairLift_comp_iso :
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.mapIso
        ((modulePullback B S hS (representedSpaceMap B S hS h)).mapIso
          (transitionOn B S hS (representedFamily B S hS T)
              (representedFamilyMap B S hS T f) D.F D.transition i j
              (representedPairLift B S hS T f a b ha hb)
              (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
              (representedPairLift_fst B S hS T f a b ha hb)
              (representedPairLift_snd B S hS T f a b ha hb)))) ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.mapIso
            ((representedModulePullbackCompIso B S hS h b).app (D.F j))) =
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.mapIso
          ((representedModulePullbackCompIso B S hS h a).app (D.F i))) ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj Y') Y'.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS Y').inverse.mapIso
            (transitionOn B S hS (representedFamily B S hS T)
                (representedFamilyMap B S hS T f) D.F D.transition i j
                (representedPairLift B S hS T f (h ≫ a) (h ≫ b) ha' hb')
                (representedSpaceMap B S hS (h ≫ a)) (representedSpaceMap B S hS (h ≫ b))
                (representedPairLift_fst B S hS T f (h ≫ a) (h ≫ b) ha' hb')
                (representedPairLift_snd B S hS T f (h ≫ a) (h ≫ b) ha' hb'))) := by
  refine Iso.ext ?_
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    restrictModule_transitionOn_representedPairLift_comp_hom B S hS T f D h a b ha hb ha' hb'

/-- **The pairwise isomorphism of a descent datum of a represented family, read on the underlying
schemes at a pair of morphisms of the site and pulled back along a third, is the one read at the
composed pair** — as an equality of isomorphisms, the two sides compared by the contraction
`AlgebraicGeometry.Scheme.Modules.pullbackComp` of the two pullbacks of modules on the schemes. -/
public theorem zariskiTransitionOn_pullbackComp_iso :
    (Scheme.Modules.pullback
        (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).mapIso
          (zariskiTransitionOn B S hS T f D a b ha hb) ≪≫
        (Scheme.Modules.pullbackComp
            (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (SmallEtale.schemeHom (associatedBigEtaleSite B) b.left)).app
            (representedZariskiModule B S hS (T j) (D.F j)) =
      (Scheme.Modules.pullbackComp
          (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
          (SmallEtale.schemeHom (associatedBigEtaleSite B) a.left)).app
            (representedZariskiModule B S hS (T i) (D.F i)) ≪≫
        zariskiTransitionOn B S hS T f D (h ≫ a) (h ≫ b) ha' hb' := by
  have key : ∀ {Y : BigFppfOver B S hS} {q : Y ⟶ U} (a : Y ⟶ T i) (b : Y ⟶ T j)
      (ha : a ≫ f i = q) (hb : b ≫ f j = q),
      zariskiTransitionOn B S hS T f D a b ha hb =
        (representedZariskiModulePullbackIso B S hS a
            (relativelyRepresentable_yoneda_map B S hS a) (D.F i) (D.quasicoherent i)) ≪≫
          ((SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj Y) Y.left.property).mapIso
            ((representedSmallEtaleModuleEquivalence B S hS Y).inverse.mapIso
              (transitionOn B S hS (representedFamily B S hS T)
                  (representedFamilyMap B S hS T f) D.F D.transition i j
                  (representedPairLift B S hS T f a b ha hb)
                  (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
                  (representedPairLift_fst B S hS T f a b ha hb)
                  (representedPairLift_snd B S hS T f a b ha hb)))) ≪≫
          (representedZariskiModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b) (D.F j)
              (D.quasicoherent j)).symm := fun _ _ _ _ => rfl
  rw [key a b ha hb, key (h ≫ a) (h ≫ b) ha' hb', Functor.mapIso_trans, Functor.mapIso_trans,
    Functor.mapIso_symm]
  exact Stacks.iso_square_paste _ _ _ _ _ _ _ _ _ _ _ _ _
    (representedZariskiModulePullbackIso_comp_iso B S hS h a
      (relativelyRepresentable_yoneda_map B S hS h)
      (relativelyRepresentable_yoneda_map B S hS a)
      (relativelyRepresentable_yoneda_map B S hS (h ≫ a)) (D.F i) (D.quasicoherent i))
    (representedZariskiModulePullbackIso_naturality_iso B S hS h
      (relativelyRepresentable_yoneda_map B S hS h)
      (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS a
          (relativelyRepresentable_yoneda_map B S hS a) (D.F i)
          (D.quasicoherent i))
      (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS b
          (relativelyRepresentable_yoneda_map B S hS b) (D.F j)
          (D.quasicoherent j))
      ((transitionOn B S hS (representedFamily B S hS T)
          (representedFamilyMap B S hS T f) D.F D.transition i j
          (representedPairLift B S hS T f a b ha hb)
          (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
          (representedPairLift_fst B S hS T f a b ha hb)
          (representedPairLift_snd B S hS T f a b ha hb))))
    (restrictModule_transitionOn_representedPairLift_comp_iso B S hS T f D h a b ha hb
      ha' hb')
    (representedZariskiModulePullbackIso_comp_iso B S hS h b
      (relativelyRepresentable_yoneda_map B S hS h)
      (relativelyRepresentable_yoneda_map B S hS b)
      (relativelyRepresentable_yoneda_map B S hS (h ≫ b)) (D.F j) (D.quasicoherent j))

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn_pullbackComp_iso` read on
the underlying morphisms. -/
public theorem zariskiTransitionOn_pullbackComp :
    (Scheme.Modules.pullback
        (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).map
          (zariskiTransitionOn B S hS T f D a b ha hb).hom ≫
        (Scheme.Modules.pullbackComp
            (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (SmallEtale.schemeHom (associatedBigEtaleSite B) b.left)).hom.app
            (representedZariskiModule B S hS (T j) (D.F j)) =
      (Scheme.Modules.pullbackComp
          (SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
          (SmallEtale.schemeHom (associatedBigEtaleSite B) a.left)).hom.app
            (representedZariskiModule B S hS (T i) (D.F i)) ≫
        (zariskiTransitionOn B S hS T f D (h ≫ a) (h ≫ b) ha' hb').hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    congrArg Iso.hom (zariskiTransitionOn_pullbackComp_iso B S hS T f D h a b ha hb ha' hb')

end Coherence

end Represented

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
