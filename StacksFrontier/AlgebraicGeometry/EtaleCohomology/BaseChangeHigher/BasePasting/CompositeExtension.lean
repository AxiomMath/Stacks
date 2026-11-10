module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.EtalePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.DerivedTransport

/-!
# Base functoriality of the étale base change comparison for a composite extension

With composites of morphisms of schemes carried as named morphisms, this file proves the
associativity pentagon of the étale inverse image comparison, re-reads the underived comparison
`smallEtaleBaseChangeAb` as a mate across the horizontal adjunctions, and proves the underived
pasting law `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_comp` and the bounded below derived
pasting law `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_comp` for a composite
extension `f'' ≫ f'`, with its consequences for the base change map on higher direct images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

section NamedComposite

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `f_* ⋙ g_* ≅ (fg)_*` for direct image of abelian sheaves on
the small étale sites, with the composite `fg` carried as a named morphism. -/
public def smallEtalePushforwardAbCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePushforwardAb f ⋙ smallEtalePushforwardAb g ≅ smallEtalePushforwardAb fg :=
  smallEtalePushforwardComp' f g fg hfg Ab.{u + 1}

/-- With the composite written out, the named-composite direct image comparison is
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso`. -/
public lemma smallEtalePushforwardAbCompIso'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePushforwardAbCompIso' f g (f ≫ g) rfl =
      smallEtalePushforwardAbCompIso f g := by
  have h : smallEtaleBaseChangeComp' f g (f ≫ g) rfl = smallEtaleBaseChangeComp f g :=
    Iso.ext (by simp [smallEtaleBaseChangeComp'])
  exact congrArg (fun z ↦ Functor.sheafPushforwardContinuousComp' (Iso.symm z)
    Ab.{u + 1} _ _ _) h

/-- The named-composite direct image comparison is the comparison at the written-out
composite, transported along the equation naming it. -/
public lemma smallEtalePushforwardAbCompIso'_eq (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePushforwardAbCompIso' f g fg hfg =
      smallEtalePushforwardAbCompIso f g ≪≫
        eqToIso (congrArg (fun m : X ⟶ Z ↦ smallEtalePushforwardAb m) hfg.symm) := by
  subst hfg
  exact (smallEtalePushforwardAbCompIso'_rfl f g).trans (Iso.ext (by simp)).symm

/-- The composition isomorphism `(f')⁻¹ ∘ (f'')⁻¹ ≅ (f'' ∘ f')⁻¹` for inverse image of
abelian sheaves on the small étale sites, with the composite carried as a named morphism. -/
public def smallEtalePullbackAbCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePullbackAb g ⋙ smallEtalePullbackAb f ≅ smallEtalePullbackAb fg :=
  Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb f)
    (smallEtaleAdjunctionAb fg) (smallEtalePushforwardAbCompIso' f g fg hfg)

/-- The named-composite inverse image comparison is the comparison of left adjoints attached
to the named-composite direct image comparison. -/
public lemma smallEtalePullbackAbCompIso'_def (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePullbackAbCompIso' f g fg hfg =
      Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb f)
        (smallEtaleAdjunctionAb fg) (smallEtalePushforwardAbCompIso' f g fg hfg) := rfl

/-- With the composite written out, the named-composite inverse image comparison is
`Stacks.EtaleCohomology.smallEtalePullbackAbTowerCompIso`. -/
public lemma smallEtalePullbackAbCompIso'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePullbackAbCompIso' f g (f ≫ g) rfl = smallEtalePullbackAbTowerCompIso f g :=
  congrArg (fun z ↦ Adjunction.leftAdjointCompIso (smallEtaleAdjunctionAb g)
      (smallEtaleAdjunctionAb f) (smallEtaleAdjunctionAb (f ≫ g)) z)
    (smallEtalePushforwardAbCompIso'_rfl f g)

/-- **The associativity pentagon of the inverse image comparison.**  It is the associativity
pentagon of the direct image comparison, read through uniqueness of left adjoints. -/
public lemma smallEtalePullbackAbCompIso'_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁)
    (hq : q = j ≫ i) (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a) :
    Functor.isoWhiskerLeft (smallEtalePullbackAb f)
          (smallEtalePullbackAbCompIso' j i q hq) ≪≫
        smallEtalePullbackAbCompIso' q f p hp₁ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtalePullbackAbCompIso' i f a ha)
            (smallEtalePullbackAb j) ≪≫
          smallEtalePullbackAbCompIso' j a p hp₂ := by
  refine Adjunction.leftAdjointCompIso_assoc (smallEtaleAdjunctionAb f)
    (smallEtaleAdjunctionAb i) (smallEtaleAdjunctionAb j) (smallEtaleAdjunctionAb a)
    (smallEtaleAdjunctionAb q) (smallEtaleAdjunctionAb p) _ _ _ _ ?_
  have hpush : Functor.isoWhiskerRight (smallEtalePushforwardAbCompIso' j i q hq)
          (smallEtalePushforwardAb f) ≪≫
        smallEtalePushforwardAbCompIso' q f p hp₁ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallEtalePushforwardAb j)
            (smallEtalePushforwardAbCompIso' i f a ha) ≪≫
          smallEtalePushforwardAbCompIso' j a p hp₂ :=
    smallEtalePushforwardComp'_assoc j i f q hq a ha p hp₁ hp₂ Ab.{u + 1}
  rw [hpush]
  exact Iso.ext (by simp)

end NamedComposite

section MateForm

variable {S T X' Y : Scheme.{u}}

/-- **The underived étale base change comparison of a commutative square is the mate, under
the two inverse-image/direct-image adjunctions of its horizontal morphisms, of the comparison
of the two composite inverse images**, with the common composite carried as a named
morphism. -/
public lemma smallEtaleBaseChangeAb_eq_mateEquiv (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X')
    (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (P : Y ⟶ S) (hPh : P = h ≫ f') (hPe : P = e ≫ g) :
    smallEtaleBaseChangeAb f' g h e w =
      mateEquiv (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
        (TwoSquare.mk _ _ _ _
          ((smallEtalePullbackAbCompIso' h f' P hPh).hom ≫
            (smallEtalePullbackAbCompIso' e g P hPe).inv)) := by
  have hdef : smallEtaleBaseChangeAb f' g h e w =
      mate (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
        (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        ((smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm)) := rfl
  have hconj : conjugateEquiv ((smallEtaleAdjunctionAb g).comp (smallEtaleAdjunctionAb e))
        ((smallEtaleAdjunctionAb f').comp (smallEtaleAdjunctionAb h))
        ((smallEtalePullbackAbCompIso' h f' P hPh).hom ≫
          (smallEtalePullbackAbCompIso' e g P hPe).inv) =
      (smallEtalePushforwardAbCompIso' e g P hPe).hom ≫
        (smallEtalePushforwardAbCompIso' h f' P hPh).inv := by
    refine (conjugateEquiv_comp
      ((smallEtaleAdjunctionAb g).comp (smallEtaleAdjunctionAb e))
      (smallEtaleAdjunctionAb P)
      ((smallEtaleAdjunctionAb f').comp (smallEtaleAdjunctionAb h))
      (smallEtalePullbackAbCompIso' e g P hPe).inv
      (smallEtalePullbackAbCompIso' h f' P hPh).hom).symm.trans ?_
    rw [smallEtalePullbackAbCompIso'_def, smallEtalePullbackAbCompIso'_def,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      conjugateEquiv_leftAdjointCompIso_hom]
  have hiso : ((smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm)).hom =
      (smallEtalePushforwardAbCompIso' e g P hPe).hom ≫
        (smallEtalePushforwardAbCompIso' h f' P hPh).inv := by
    rw [smallEtalePushforwardAbCompIso'_eq, smallEtalePushforwardAbCompIso'_eq]
    simp
  have key : mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')
        (mateEquiv (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
          (TwoSquare.mk _ _ _ _
            ((smallEtalePullbackAbCompIso' h f' P hPh).hom ≫
              (smallEtalePullbackAbCompIso' e g P hPe).inv))) =
      TwoSquare.mk _ _ _ _
        ((smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm)).hom :=
    (iterated_mateEquiv_conjugateEquiv (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
          (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e) _).trans
      (hconj.trans hiso.symm)
  rw [hdef, mate_eq_mateEquiv_symm, ← key, Equiv.symm_apply_apply]

end MateForm

section Composition

variable {S T X' X'' Y Y'' : Scheme.{u}}

/-- **The inverse image comparisons of a tower of two commutative squares paste**, as an
identity of 2-squares.  It is the associativity pentagon of the inverse image comparison, used
for the three chains `Y'' → X'' → X' → S`, `Y'' → Y → X' → S` and `Y'' → Y → T → S`. -/
private theorem pullbackComparison_hComp (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (a : X'' ⟶ S) (ha : a = f'' ≫ f') (b : Y'' ⟶ T) (hb : b = e'' ≫ e)
    (P₁ : Y ⟶ S) (hP₁h : P₁ = h ≫ f') (hP₁e : P₁ = e ≫ g)
    (P₂ : Y'' ⟶ X') (hP₂h : P₂ = h'' ≫ f'') (hP₂e : P₂ = e'' ≫ h)
    (P : Y'' ⟶ S) (hPa : P = h'' ≫ a) (hPb : P = b ≫ g)
    (hPP₂ : P = P₂ ≫ f') (hPe : P = e'' ≫ P₁) :
    TwoSquare.hComp
        (TwoSquare.mk (smallEtalePullbackAb f') (smallEtalePullbackAb g)
          (smallEtalePullbackAb h) (smallEtalePullbackAb e)
          ((smallEtalePullbackAbCompIso' h f' P₁ hP₁h).hom ≫
            (smallEtalePullbackAbCompIso' e g P₁ hP₁e).inv))
        (TwoSquare.mk (smallEtalePullbackAb f'') (smallEtalePullbackAb h)
          (smallEtalePullbackAb h'') (smallEtalePullbackAb e'')
          ((smallEtalePullbackAbCompIso' h'' f'' P₂ hP₂h).hom ≫
            (smallEtalePullbackAbCompIso' e'' h P₂ hP₂e).inv)) =
      TwoSquare.whiskerBottom
        (TwoSquare.whiskerTop
          (TwoSquare.mk (smallEtalePullbackAb a) (smallEtalePullbackAb g)
            (smallEtalePullbackAb h'') (smallEtalePullbackAb b)
            ((smallEtalePullbackAbCompIso' h'' a P hPa).hom ≫
              (smallEtalePullbackAbCompIso' b g P hPb).inv))
          (smallEtalePullbackAbCompIso' f'' f' a ha).hom)
        (smallEtalePullbackAbCompIso' e'' e b hb).inv := by
  have hA1 := smallEtalePullbackAbCompIso'_assoc f' f'' h'' a ha P₂ hP₂h P hPP₂ hPa
  have hA2 := smallEtalePullbackAbCompIso'_assoc f' h e'' P₁ hP₁h P₂ hP₂e P hPP₂ hPe
  have hA3 := smallEtalePullbackAbCompIso'_assoc g e e'' P₁ hP₁e b hb P hPb hPe
  simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  exact pentagonChase
    (Functor.associator (smallEtalePullbackAb f') (smallEtalePullbackAb f'')
      (smallEtalePullbackAb h''))
    (Functor.associator (smallEtalePullbackAb f') (smallEtalePullbackAb h)
      (smallEtalePullbackAb e''))
    (Functor.associator (smallEtalePullbackAb g) (smallEtalePullbackAb e)
      (smallEtalePullbackAb e''))
    (Functor.isoWhiskerLeft (smallEtalePullbackAb f')
      (smallEtalePullbackAbCompIso' h'' f'' P₂ hP₂h))
    (Functor.isoWhiskerLeft (smallEtalePullbackAb f')
      (smallEtalePullbackAbCompIso' e'' h P₂ hP₂e))
    (Functor.isoWhiskerRight (smallEtalePullbackAbCompIso' h f' P₁ hP₁h)
      (smallEtalePullbackAb e''))
    (Functor.isoWhiskerRight (smallEtalePullbackAbCompIso' e g P₁ hP₁e)
      (smallEtalePullbackAb e''))
    (smallEtalePullbackAbCompIso' P₂ f' P hPP₂)
    (smallEtalePullbackAbCompIso' e'' P₁ P hPe)
    (smallEtalePullbackAbCompIso' h'' a P hPa)
    (smallEtalePullbackAbCompIso' b g P hPb)
    (Functor.isoWhiskerLeft (smallEtalePullbackAb g)
      (smallEtalePullbackAbCompIso' e'' e b hb))
    (Functor.whiskerRight (smallEtalePullbackAbCompIso' f'' f' a ha).hom
      (smallEtalePullbackAb h''))
    (congrArg Iso.hom hA1) (congrArg Iso.hom hA2) (congrArg Iso.hom hA3)

/-- **The underived étale base change comparisons of a tower of two commutative squares
compose.**  For a square `h ≫ f' = e ≫ g` and a second one `h'' ≫ f'' = e'' ≫ h` extending
its base, the comparison attached to the outer rectangle is the comparison of the first square
carried by `(f'')⁻¹` followed by the comparison of the second, read through the composition
isomorphisms of the inverse images.  Nothing is assumed of the squares beyond
commutativity. -/
public theorem smallEtaleBaseChangeAb_comp' (f' : X' ⟶ S) (f'' : X'' ⟶ X') (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (a : X'' ⟶ S) (ha : a = f'' ≫ f') (b : Y'' ⟶ T) (hb : b = e'' ≫ e)
    (wab : h'' ≫ a = b ≫ g) :
    pasteTrans (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
        (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
        (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w') =
      Functor.whiskerLeft (smallEtalePushforwardAb g)
          (smallEtalePullbackAbCompIso' f'' f' a ha).hom ≫
        smallEtaleBaseChangeAb a g h'' b wab ≫
          Functor.whiskerRight (smallEtalePullbackAbCompIso' e'' e b hb).inv
            (smallEtalePushforwardAb h'') := by
  have hPP₂ : h'' ≫ a = (h'' ≫ f'') ≫ f' := by rw [ha, Category.assoc]
  have hPe : h'' ≫ a = e'' ≫ (h ≫ f') := by
    rw [wab, hb, Category.assoc, w]
  have e1 := smallEtaleBaseChangeAb_eq_mateEquiv f' g h e w (h ≫ f') rfl w
  have e2 := smallEtaleBaseChangeAb_eq_mateEquiv f'' h h'' e'' w' (h'' ≫ f'') rfl w'
  have e3 := smallEtaleBaseChangeAb_eq_mateEquiv a g h'' b wab (h'' ≫ a) rfl wab
  have hmain :=
    (mateEquiv_vcomp (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
        (smallEtaleAdjunctionAb h'')
        (TwoSquare.mk (smallEtalePullbackAb f') (smallEtalePullbackAb g)
          (smallEtalePullbackAb h) (smallEtalePullbackAb e)
          ((smallEtalePullbackAbCompIso' h f' (h ≫ f') rfl).hom ≫
            (smallEtalePullbackAbCompIso' e g (h ≫ f') w).inv))
        (TwoSquare.mk (smallEtalePullbackAb f'') (smallEtalePullbackAb h)
          (smallEtalePullbackAb h'') (smallEtalePullbackAb e'')
          ((smallEtalePullbackAbCompIso' h'' f'' (h'' ≫ f'') rfl).hom ≫
            (smallEtalePullbackAbCompIso' e'' h (h'' ≫ f'') w').inv))).symm.trans
      ((congrArg (fun α ↦ mateEquiv (smallEtaleAdjunctionAb g)
            (smallEtaleAdjunctionAb h'') α)
          (pullbackComparison_hComp f' f'' g h e h'' e'' a ha b hb (h ≫ f') rfl w
            (h'' ≫ f'') rfl w' (h'' ≫ a) rfl wab hPP₂ hPe)).trans
        (mateEquiv_whisker (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h'')
          (TwoSquare.mk (smallEtalePullbackAb a) (smallEtalePullbackAb g)
            (smallEtalePullbackAb h'') (smallEtalePullbackAb b)
            ((smallEtalePullbackAbCompIso' h'' a (h'' ≫ a) rfl).hom ≫
              (smallEtalePullbackAbCompIso' b g (h'' ≫ a) wab).inv))
          (smallEtalePullbackAbCompIso' f'' f' a ha).hom
          (smallEtalePullbackAbCompIso' e'' e b hb).inv))
  have hN :
      (Functor.associator (smallEtalePushforwardAb g) (smallEtalePullbackAb f')
            (smallEtalePullbackAb f'')).inv ≫
          Functor.whiskerRight (smallEtaleBaseChangeAb f' g h e w)
            (smallEtalePullbackAb f'') ≫
          (Functor.associator (smallEtalePullbackAb e) (smallEtalePushforwardAb h)
            (smallEtalePullbackAb f'')).hom ≫
          Functor.whiskerLeft (smallEtalePullbackAb e)
            (smallEtaleBaseChangeAb f'' h h'' e'' w') ≫
          (Functor.associator (smallEtalePullbackAb e) (smallEtalePullbackAb e'')
            (smallEtalePushforwardAb h'')).inv =
        (Functor.whiskerLeft (smallEtalePushforwardAb g)
              (smallEtalePullbackAbCompIso' f'' f' a ha).hom ≫
            smallEtaleBaseChangeAb a g h'' b wab) ≫
          Functor.whiskerRight (smallEtalePullbackAbCompIso' e'' e b hb).inv
            (smallEtalePushforwardAb h'') := by
    rw [e1, e2, e3]
    exact hmain
  refine NatTrans.ext (funext fun Z ↦ ?_)
  have hZ := NatTrans.congr_app hN Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] at hZ
  simpa only [pasteTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using hZ

/-- **The underived étale base change comparisons of a tower of two commutative squares
compose**, with the two composites written out. -/
public theorem smallEtaleBaseChangeAb_comp (f' : X' ⟶ S) (f'' : X'' ⟶ X') (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g) :
    pasteTrans (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        (smallEtalePushforwardAb h'') (smallEtalePullbackAb f') (smallEtalePullbackAb e)
        (smallEtalePullbackAb f'') (smallEtalePullbackAb e'')
        (smallEtaleBaseChangeAb f' g h e w) (smallEtaleBaseChangeAb f'' h h'' e'' w') =
      Functor.whiskerLeft (smallEtalePushforwardAb g)
          (smallEtalePullbackAbTowerCompIso f'' f').hom ≫
        smallEtaleBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'' ≫
          Functor.whiskerRight (smallEtalePullbackAbTowerCompIso e'' e).inv
            (smallEtalePushforwardAb h'') := by
  rw [← smallEtalePullbackAbCompIso'_rfl f'' f', ← smallEtalePullbackAbCompIso'_rfl e'' e]
  exact smallEtaleBaseChangeAb_comp' f' f'' g h e h'' e'' w w' (f'' ≫ f') rfl (e'' ≫ e) rfl w''

end Composition

section DerivedComposition

variable {S T X' X'' Y Y'' : Scheme.{u}}

/-- **Base functoriality of the bounded below derived étale base change comparison, in the
form the pasting law and the transport law produce it.**  The comparison of the first square
carried by `R(f'')⁻¹`, followed by the comparison of the second, read through the composition
isomorphisms of the derived inverse images of the two *pairs* of morphisms, is the comparison
of the composite extension, conjugated by the right derived functors of the underived
composition isomorphisms. -/
public theorem smallEtaleDerivedBaseChangeAb_comp_fac (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g) :
    Functor.whiskerLeft (smallEtalePushforwardAb g).rightDerivedFunctorPlus
          (smallEtaleDerivedPullbackCompIso f' f'').hom ≫
        Functor.whiskerRight (smallEtaleDerivedBaseChangeAb f' g h e w)
            (smallEtalePullbackAb f'').rightDerivedFunctorPlus ≫
          Functor.whiskerLeft (smallEtalePullbackAb e).rightDerivedFunctorPlus
              (smallEtaleDerivedBaseChangeAb f'' h h'' e'' w') ≫
            Functor.whiskerRight (smallEtaleDerivedPullbackCompIso e e'').inv
              (smallEtalePushforwardAb h'').rightDerivedFunctorPlus =
      Functor.whiskerLeft (smallEtalePushforwardAb g).rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusNatIso
            (smallEtalePullbackAbTowerCompIso f'' f')).hom ≫
        smallEtaleDerivedBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'' ≫
          Functor.whiskerRight
            (Functor.rightDerivedFunctorPlusNatIso
              (smallEtalePullbackAbTowerCompIso e'' e)).inv
            (smallEtalePushforwardAb h'').rightDerivedFunctorPlus := by
  have htr := derived_transport (smallEtalePushforwardAb g) (smallEtalePushforwardAb h'')
    (smallEtalePullbackAbTowerCompIso f'' f') (smallEtalePullbackAbTowerCompIso e'' e)
    (smallEtaleBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'')
  rw [← smallEtaleBaseChangeAb_comp f' f'' g h e h'' e'' w w' w'',
    ← smallEtaleDerivedBaseChangeAb_eq] at htr
  exact (smallEtaleDerivedBaseChangeAb_paste f' f'' g h e h'' e'' w w').symm.trans htr

/-- The forward composition isomorphism of the derived inverse images, written out. -/
public lemma smallEtaleDerivedPullbackComp_hom (f'' : X'' ⟶ X') (f' : X' ⟶ S) :
    (smallEtaleDerivedPullbackComp f'' f').hom =
      (Functor.rightDerivedFunctorPlusNatIso
          (smallEtalePullbackAbTowerCompIso f'' f')).inv ≫
        (smallEtaleDerivedPullbackCompIso f' f'').hom := rfl

/-- The inverse composition isomorphism of the derived inverse images, written out. -/
public lemma smallEtaleDerivedPullbackComp_inv (f'' : X'' ⟶ X') (f' : X' ⟶ S) :
    (smallEtaleDerivedPullbackComp f'' f').inv =
      (smallEtaleDerivedPullbackCompIso f' f'').inv ≫
        (Functor.rightDerivedFunctorPlusNatIso
          (smallEtalePullbackAbTowerCompIso f'' f')).hom := rfl

/-- **Base functoriality of the bounded below derived étale base change comparison.**  For a
commutative square `h ≫ f' = e ≫ g` of schemes and a second one `h'' ≫ f'' = e'' ≫ h`
extending its base along `f''`, the comparison attached to the composite extension is the
comparison of the first square carried by `R(f'')⁻¹`, followed by the comparison of the
second, read through the composition isomorphisms `R(f'' ∘ f')⁻¹ ≅ R(f')⁻¹ ⋙ R(f'')⁻¹` and
`R(e'' ∘ e)⁻¹ ≅ Re⁻¹ ⋙ R(e'')⁻¹`. -/
public theorem smallEtaleDerivedBaseChangeAb_comp (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g) :
    smallEtaleDerivedBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'' =
      Functor.whiskerLeft (smallEtalePushforwardAb g).rightDerivedFunctorPlus
          (smallEtaleDerivedPullbackComp f'' f').hom ≫
        Functor.whiskerRight (smallEtaleDerivedBaseChangeAb f' g h e w)
            (smallEtalePullbackAb f'').rightDerivedFunctorPlus ≫
          Functor.whiskerLeft (smallEtalePullbackAb e).rightDerivedFunctorPlus
              (smallEtaleDerivedBaseChangeAb f'' h h'' e'' w') ≫
            Functor.whiskerRight (smallEtaleDerivedPullbackComp e'' e).inv
              (smallEtalePushforwardAb h'').rightDerivedFunctorPlus := by
  have hsolve := cancelIsos
    (Functor.isoWhiskerLeft (smallEtalePushforwardAb g).rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusNatIso (smallEtalePullbackAbTowerCompIso f'' f')))
    (Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusNatIso (smallEtalePullbackAbTowerCompIso e'' e))
      (smallEtalePushforwardAb h'').rightDerivedFunctorPlus) _ _
    (smallEtaleDerivedBaseChangeAb_comp_fac f' f'' g h e h'' e'' w w' w'')
  rw [hsolve, smallEtaleDerivedPullbackComp_hom, smallEtaleDerivedPullbackComp_inv]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]

/-- **Two out of three for the bounded below derived étale base change comparison.**  If the
comparisons of the two squares are invertible at the relevant objects, so is the comparison of
the composite extension. -/
public theorem isIso_smallEtaleDerivedBaseChangeAb_comp_app (f' : X' ⟶ S) (f'' : X'' ⟶ X')
    (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'') (e'' : Y'' ⟶ Y)
    (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g)
    (Z : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (h₁ : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app Z))
    (h₂ : IsIso ((smallEtaleDerivedBaseChangeAb f'' h h'' e'' w').app
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj Z))) :
    IsIso ((smallEtaleDerivedBaseChangeAb (f'' ≫ f') g h'' (e'' ≫ e) w'').app Z) := by
  have := h₁
  have := h₂
  rw [NatTrans.congr_app
    (smallEtaleDerivedBaseChangeAb_comp f' f'' g h e h'' e'' w w' w'') Z]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **The degree-`q` base change map of a composite extension.**  If the derived comparisons
of the two squares are invertible at the sheaf placed in degree zero and at its derived
inverse image, then the base change map on higher direct images of [Stacks, Tag 0F02] for the
composite extension is invertible in every degree. -/
public theorem isIso_higherBaseChangeMapAb_app_of_isIso_derived_comp (f' : X' ⟶ S)
    (f'' : X'' ⟶ X') (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (h'' : Y'' ⟶ X'')
    (e'' : Y'' ⟶ Y) (w : h ≫ f' = e ≫ g) (w' : h'' ≫ f'' = e'' ≫ h)
    (w'' : h'' ≫ (f'' ≫ f') = (e'' ≫ e) ≫ g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (h₁ : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)))
    (h₂ : IsIso ((smallEtaleDerivedBaseChangeAb f'' h h'' e'' w').app
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F))))
    (q : ℕ) :
    IsIso ((higherBaseChangeMapAb (f'' ≫ f') g h'' (e'' ≫ e) w'' q).app F) :=
  isIso_higherBaseChangeMapAb_app_of_isIso_derived (f'' ≫ f') g h'' (e'' ≫ e) w'' F
    (isIso_smallEtaleDerivedBaseChangeAb_comp_app f' f'' g h e h'' e'' w w' w'' _ h₁ h₂) q

end DerivedComposition

end Stacks.EtaleCohomology

end
